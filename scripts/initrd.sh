#!/bin/bash

# Create a directory for our rootfs
mkdir my_rootfs
cd my_rootfs

# Create basic filesystem layout
mkdir -p bin sbin etc proc sys dev

# Copy busybox into our rootfs
cp $(which busybox) ./bin/

# Link busybox to common commands
for cmd in $(./bin/busybox --list); do
  ln -s /bin/busybox ./bin/$cmd
done
# Also for sbin commands
ln -s /bin/busybox ./sbin/init

# Create a minimal init script. This will be the first process (PID 1).
# It mounts necessary pseudo-filesystems and starts a shell.
cat > ./init <<EOF
#!/bin/sh
mount -t proc none /proc
mount -t sysfs none /sys
mount -t devtmpfs none /dev

echo "=============================="
echo " Welcome to Minimal Linux!"
echo "=============================="

# Start an interactive shell
exec /bin/sh
EOF

chmod +x ./init

# Pack it into a gzipped CPIO archive (the initramfs)
echo "Creating initramfs.cpio.gz..."
find . | cpio -o -H newc | gzip > ../build/initramfs.cpio.gz
echo "Done."

cd ..