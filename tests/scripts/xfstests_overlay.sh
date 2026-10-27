#!/bin/bash

current_dir=$(dirname $(realpath $0))

sudo apt-get update
sudo apt-get install acl attr automake bc dbench dump e2fsprogs fio gawk \
    gcc git indent libacl1-dev libaio-dev libcap-dev libgdbm-dev libtool \
    libtool-bin liburing-dev libuuid1 lvm2 make psmisc python3 quota sed \
    uuid-dev uuid-runtime xfsprogs linux-headers-$(uname -r) sqlite3
sudo apt-get install exfatprogs f2fs-tools ocfs2-tools udftools xfsdump \
    xfslibs-dev

# clone xfstests and install.
cd /tmp/
git clone -b v2026.10.15 git://git.kernel.org/pub/scm/fs/xfs/xfstests-dev.git
cd xfstests-dev
# Keep building with the long-standing gnu17 dialect: runners ship a GCC whose
# default is C23, where an empty parameter list means (void), and the ltp-derived
# helpers are not guaranteed C23-clean. configure picks up CFLAGS from the
# environment, and builddefs appends the platform flags on top of it.
export CFLAGS="-g -O2 -std=gnu17"
make
sudo make install
# overwrite local config.
cat >local.config  <<EOF
export TEST_DEV=testoverlay
export TEST_DIR=/tmp/testoverlay/merged
#export SCRATCH_DEV=testoverlay
#export SCRATCH_MNT=/tmp/test2/merged
export FSTYP=fuse
export FUSE_SUBTYP=.testoverlay
EOF

# create fuse overlay mount script.
# /tmp/testoverlay must exists.
sudo cat >/usr/sbin/mount.fuse.testoverlay  <<EOF
#!/bin/bash

ulimit -n 1048576
exec /usr/sbin/overlay -o \
    lowerdir=/tmp/testoverlay/lower2:/tmp/testoverlay/lower1,upperdir=/tmp/testoverlay/upper,workdir=/tmp/testoverlay/work \
    testoverlay /tmp/testoverlay/merged \
    1>>/tmp/testoverlay.log 2>&1 &
sleep 1
EOF
sudo chmod +x /usr/sbin/mount.fuse.testoverlay

# create related directories.
mkdir -p /tmp/testoverlay/{upper,work,merged,lower2,lower1}

echo "====> Start to run xfstests."
# run tests.
cd /tmp/xfstests-dev
# Some tests are not supported by fuse or cannot pass currently.
sudo ./check -fuse -E $current_dir/xfstests_overlay.exclude


