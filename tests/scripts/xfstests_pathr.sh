#!/bin/bash
#
# Run xfstests as root against the passthrough test daemon in tests/passthrough,
# which serves /tmp/pathr_src at /tmp/pathr_dst.
#
# Usage: xfstests_pathr.sh [mode [check arguments]]
#
# The mode selects the daemon options, see `passthrough --help`:
#   default             the daemon's own service threads, writeback cache on
#   sync                SyncFuseServing
#   async-tokio         AsyncFuseServing on the tokio runtime
#   async-tokio-uring   AsyncFuseServing on the tokio-uring runtime
#   uring               UringFuseServing, which needs Linux 6.14+ with the fuse
#                       module parameter enable_uring on
#   no-writeback        the default with the writeback cache off
#   kernel-passthrough  kernel passthrough with the writeback cache off,
#                       Linux 6.9+
# Every mode skips the tests in xfstests_pathr.exclude, and a mode with an
# xfstests_pathr.<mode>.exclude next to it also skips those. Further
# arguments go to xfstests' check, such as the tests to run.
#
# Without XFSTESTS_CHECK the script installs packages with apt-get and builds
# xfstests in /tmp/xfstests-dev. These variables let it run elsewhere:
#   XFSTESTS_CHECK    an xfstests check to run from the current directory
#                     instead, such as ./check in a built tree or nixpkgs'
#                     xfstests-check
#   PASSTHROUGH_BIN   the daemon (default /usr/sbin/passthrough)
#   MOUNT_HELPER_DIR  where to put mount.fuse.testpassthrough, a directory
#                     that mount(8) searches for helpers (default /usr/sbin)

current_dir=$(dirname "$(realpath "$0")")
mode=${1:-default}
shift
PASSTHROUGH_BIN=${PASSTHROUGH_BIN:-/usr/sbin/passthrough}
MOUNT_HELPER_DIR=${MOUNT_HELPER_DIR:-/usr/sbin}

case "${mode}" in
    default) daemon_args="" ;;
    sync) daemon_args="--serving sync" ;;
    async-tokio) daemon_args="--serving async --runtime tokio" ;;
    async-tokio-uring) daemon_args="--serving async --runtime uring" ;;
    uring) daemon_args="--serving uring" ;;
    no-writeback) daemon_args="--no-writeback" ;;
    kernel-passthrough) daemon_args="--kernel-passthrough" ;;
    *)
        echo "unknown mode ${mode}" >&2
        exit 1
        ;;
esac

if [ -z "${XFSTESTS_CHECK}" ]; then
    sudo apt-get update
    sudo apt-get install acl attr automake bc dbench dump e2fsprogs fio gawk \
        gcc git indent libacl1-dev libaio-dev libcap-dev libgdbm-dev libtool \
        libtool-bin liburing-dev libuuid1 lvm2 make psmisc python3 quota sed \
        uuid-dev uuid-runtime xfsprogs "linux-headers-$(uname -r)" sqlite3 \
        exfatprogs f2fs-tools ocfs2-tools udftools xfsdump \
        xfslibs-dev

    # clone xfstests and install.
    cd /tmp/ || exit 1
    "$current_dir"/xfstests_clone.sh || exit 1
    cd xfstests-dev || exit 1
    # Keep building with the long-standing gnu17 dialect: runners ship a GCC whose
    # default is C23, where an empty parameter list means (void), and the ltp-derived
    # helpers are not guaranteed C23-clean. configure picks up CFLAGS from the
    # environment, and builddefs appends the platform flags on top of it.
    export CFLAGS="-g -O2 -std=gnu17"
    make
    sudo make install
    XFSTESTS_CHECK=./check
fi

# Pass the configuration through HOST_OPTIONS, so that a local.config that
# xfstests_overlay.sh left in the xfstests tree can't override it.
export HOST_OPTIONS=/tmp/xfstests_pathr.config
cat >"${HOST_OPTIONS}" <<EOF
export TEST_DEV=testpassthrough
export TEST_DIR=/tmp/pathr_dst
export FSTYP=fuse
export FUSE_SUBTYP=.testpassthrough
EOF

# create the mount helper, which runs with this script's bash.
cat >"${MOUNT_HELPER_DIR}/mount.fuse.testpassthrough" <<EOF
#!${BASH}

# mount(8) may run helpers without PATH.
export PATH="${PATH}"
ulimit -n 1048576
exec "${PASSTHROUGH_BIN}" /tmp/pathr_src /tmp/pathr_dst ${daemon_args} \
    1>>/tmp/testpassthrough.log 2>&1 &
sleep 1
EOF
chmod +x "${MOUNT_HELPER_DIR}/mount.fuse.testpassthrough"

# create related dirs.
mkdir -p /tmp/pathr_src /tmp/pathr_dst

echo "====> Start to run xfstests in mode ${mode}."
# Some tests are not supported by fuse or cannot pass currently.
"${XFSTESTS_CHECK}" -fuse -E "${current_dir}/xfstests_pathr.exclude" \
    -E "${current_dir}/xfstests_pathr.${mode}.exclude" "$@"
