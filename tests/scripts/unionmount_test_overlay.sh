#!/bin/bash

# create fuse overlay mount script.
# /tmp/testoverlay must exists.
sudo cat >/usr/sbin/mount.fuse.testoverlay  <<EOF
#!/bin/bash

ulimit -n 1048576
exec /usr/sbin/overlay \$@ -l info 1>>/tmp/testoverlay.log 2>&1 &
sleep 1
EOF
sudo chmod +x /usr/sbin/mount.fuse.testoverlay


# clone xfstests and install.
cd /tmp/
git clone -b ci-fuse-backend-rs https://github.com/WeiZhang555/unionmount-testsuite.git
cd unionmount-testsuite

echo "====> Start to run unionmount-testsuite."

mkdir -p /tmp/unionmount/
touch /tmp/summary
success=0
fail=0

for testcase in dir-open-dir \
dir-open \
dir-sym1-open \
dir-sym1-weird-open \
dir-sym2-open \
dir-sym2-weird-open \
dir-weird-open \
hard-link-dir \
hard-link \
hard-link-sym \
impermissible \
mkdir \
noent-creat-excl \
noent-creat-excl-trunc \
noent-creat \
noent-creat-trunc \
noent-plain \
noent-trunc \
open-creat-excl \
open-creat-excl-trunc \
open-creat \
open-creat-trunc \
open-plain \
open-trunc \
readlink \
rename-exdev \
rmdir \
rmtree-new \
rmtree \
sym1-creat-excl \
sym1-creat \
sym1-plain \
sym1-trunc \
sym2-creat-excl \
sym2-creat \
sym2-plain \
sym2-trunc \
symx-creat-excl \
symx-creat \
symx-creat-trunc \
symx-plain \
symx-trunc \
truncate \
unlink
# === Some test cases are not supported by unionmount currently ===
# dir-weird-open-dir
# rename-dir
# rename-empty-dir
# rename-file
# rename-hard-link
# rename-mass-2
# rename-mass-3
# rename-mass-4
# rename-mass-5
# rename-mass-dir
# rename-mass
# rename-mass-sym
# rename-move-dir
# rename-new-dir
# rename-new-pop-dir
# rename-pop-dir
do
	UNIONMOUNT_BASEDIR=/tmp/unionmount sudo -E ./run --ov --fuse=testoverlay --xdev $testcase
	if [ $? -eq 0 ]
	then
		echo "===== SUCCESS: " $testcase >> /tmp/summary
		let success+=1
	else
		echo ">>>>>>>> FAIL: " $testcase >> /tmp/summary
		let fail+=1
	fi
done;

cat /tmp/summary && rm /tmp/summary
echo "Total: success: $success, fail: $fail"

if [ $fail -gt 0 ]
then
    exit 1
fi
