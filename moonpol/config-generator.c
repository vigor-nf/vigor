// Compile without any special flags, redirect output to a file, and you have your config

#include <assert.h>
#include <stdio.h>
#include <arpa/inet.h>

int main(int argc, char *argv[]) {
  struct in_addr base;
  assert(inet_aton("192.168.6.5", &base));
  for (int offset = 0; offset < 64000; offset++) {
    struct in_addr ip;
    ip.s_addr = htonl(ntohl(base.s_addr) + offset);
    printf("%s/32\t15000000\n", inet_ntoa(ip));
  }

  assert(inet_aton("10.0.0.1", &base));
  for (int offset = 0; offset < 1000; offset++) {
    struct in_addr ip;
    ip.s_addr = htonl(ntohl(base.s_addr) + offset);
    printf("%s/32\t15000000\n", inet_ntoa(ip));
  }
}
