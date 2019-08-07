FROM ubuntu:bionic

# Linux version (WITHOUT the -generic)
ARG kernel_ver

# Get the kernel stuff (since Docker shares the kernel with the host)
COPY /usr/src/linux-headers-${kernel_ver} /usr/src/linux-headers-${kernel_ver}
COPY /usr/src/linux-headers-${kernel_ver}-generic /usr/src/linux-headers-${kernel_ver}-generic
COPY /lib/modules/${kernel_ver}-generic /lib/modules/${kernel_ver}-generic

# The install script requires sudo (no need to clean apt cache, the setup script will install stuff)
RUN apt-get update && apt-get install -y sudo

# Create (-m == with a homedir) and use an user with passwordless sudo
RUN useradd -m vigor \
 && echo "vigor:vigor" | chpasswd \
 && echo 'vigor ALL=(root) NOPASSWD: ALL' >> /etc/sudoers
USER vigor
WORKDIR /home/vigor

# Copy everything from the repo
COPY . /home/vigor/
# (except for /usr and /lib mount points)
RUN rm -rf /home/vigor/vigor/lib && rm -rf /home/vigor/vigor/usr
# Give the right permissions
RUN sudo chown -R vigor:vigor *
# Execute the setup script
RUN /home/vigor/setup.sh

# Pass -l to bash so it reads ~/.profile
ENTRYPOINT ["/bin/bash", "-l"]
