#!/bin/bash
#
# Check out xfstests v2026.10.15 into ./xfstests-dev. git.kernel.org is often
# unreachable from CI runners, so first fetch the tag's commit from the GitHub
# mirror, which lacks the tag, and fall back to cloning the tag from kernel.org.

tag=v2026.10.15
commit=d07dca72d2455f4ba8c660ad4c008541ccccb707

if ! { git init -q xfstests-dev &&
    git -C xfstests-dev fetch --depth 1 https://github.com/kdave/xfstests.git "$commit" &&
    git -C xfstests-dev checkout -q --detach FETCH_HEAD; }; then
    rm -rf xfstests-dev
    for i in 1 2 3; do
        git clone -b "$tag" https://git.kernel.org/pub/scm/fs/xfs/xfstests-dev.git && break
        [ "$i" = 3 ] && exit 1
        sleep 10
    done
fi

head=$(git -C xfstests-dev rev-parse HEAD)
if [ "$head" != "$commit" ]; then
    echo "xfstests-dev is at $head, not $tag ($commit)" >&2
    exit 1
fi
