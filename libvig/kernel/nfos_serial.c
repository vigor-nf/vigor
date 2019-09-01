#include <stdint.h>

#include "nfos_portio.h"
#include "nfos_serial.h"

struct SerialPort {
  uint16_t base;
} serial_port;

static const uint16_t DEFAULT_SERIAL_PORT_BASE = 0x3F8;
static const uint8_t SERIAL_OUTPUT_EMPTY = 1 << 5;

#define data_port(sp) ((sp).base)
#define int_en_port(sp) ((sp).base + 1)
#define fifo_ctrl_port(sp) ((sp).base + 2)
#define line_ctrl_port(sp) ((sp).base + 3)
#define modem_ctrl_port(sp) ((sp).base + 4)
#define line_sts_port(sp) ((sp).base + 5)

static int nfos_serial_has_output(void) {
  return (nfos_inb(line_sts_port(serial_port)) & SERIAL_OUTPUT_EMPTY) == 0;
}

void nfos_serial_init(void) {
  serial_port.base = DEFAULT_SERIAL_PORT_BASE;

  nfos_outb(0x00, int_en_port(serial_port));
  nfos_outb(0x80, line_ctrl_port(serial_port));
  nfos_outb(0x03, data_port(serial_port));
  nfos_outb(0x00, int_en_port(serial_port));
  nfos_outb(0x03, line_ctrl_port(serial_port));
  nfos_outb(0xc7, fifo_ctrl_port(serial_port));
  nfos_outb(0x0b, modem_ctrl_port(serial_port));
  nfos_outb(0x01, int_en_port(serial_port));
}

void nfos_serial_write_char(char c) {
  // Convert LF into CRLF
  if (c == '\n') {
    nfos_serial_write_char('\r');
  }

  if (c == 8 || c == 0x7f) {
    while (nfos_serial_has_output()) {
      ;
    }
    nfos_outb(0x08, data_port(serial_port));

    while (nfos_serial_has_output()) {
      ;
    }
    nfos_outb(' ', data_port(serial_port));

    while (nfos_serial_has_output()) {
      ;
    }
    nfos_outb(0x08, data_port(serial_port));
  } else {
    while (nfos_serial_has_output()) {
      ;
    }
    nfos_outb(c, data_port(serial_port));
  }
}

void nfos_serial_write_str(const char *s) {
  for (const char *p = s; *p != '\0'; p++) {
    nfos_serial_write_char(*p);
  }
}

void nfos_serial_write_int(int x) {
  if (x < 0) {
    nfos_serial_write_char('-');
    x = -x;
  }

  static char buf[32] = { 0 };

  int i = 30;

  for (; x && i; --i, x /= 10) {
    buf[i] = '0' + (x % 10);
  }

  nfos_serial_write_str(&buf[i + 1]);
}
