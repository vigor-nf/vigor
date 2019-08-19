// Compile without any special flags, run, redirect output to a file,
// and you have your config (which we provide pre-generated)

#include <stdio.h>
#include <stdint.h>
#include <arpa/inet.h>

int main(int argc, char *argv[]) {
  for (uint32_t n = 0; n <= 65535; n++) {
    struct in_addr ip;
    ip.s_addr = htonl(n);
    printf("%s/32\t15000000\n", inet_ntoa(ip));
  }

  return 0;
}
