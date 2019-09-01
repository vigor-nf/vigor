#include <stdint.h>
#include "nfos_vga.h"

#define VGA_HEIGHT 25
#define VGA_WIDTH 80

struct vga_char {
  uint8_t ascii_char;
  uint8_t color_code;
};

static volatile struct vga_char (*volatile const VGA_BUFFER)[VGA_WIDTH] =
    (volatile struct vga_char(*volatile const)[VGA_WIDTH])0xb8000;
static int VGA_COLUMN_POS = 0;

/* Yellow foreground, black background */
#define VGA_COLOR_CODE 14

static void nfos_vga_clear_row(int row) {
  static const struct vga_char blank = {
    .ascii_char = (uint8_t)' ',
    .color_code = VGA_COLOR_CODE,
  };

  for (int i = 0; i < VGA_WIDTH; i++) {
    VGA_BUFFER[row][i] = blank;
  }
}

static void nfos_vga_newline() {
  for (int i = 1; i < VGA_HEIGHT; i++) {
    for (int j = 0; j < VGA_WIDTH; j++) {
      struct vga_char c = VGA_BUFFER[i][j];
      VGA_BUFFER[i - 1][j] = c;
    }
  }

  nfos_vga_clear_row(VGA_HEIGHT - 1);
  VGA_COLUMN_POS = 0;
}

static void nfos_vga_write_byte(uint8_t c) {
  if (c == (uint8_t)'\n') {
    nfos_vga_newline();
  } else {
    if (VGA_COLUMN_POS >= VGA_WIDTH) {
      nfos_vga_newline();
    }

    int row = VGA_HEIGHT - 1;
    int col = VGA_COLUMN_POS;

    struct vga_char vga_c = {
      .ascii_char = c,
      .color_code = VGA_COLOR_CODE,
    };

    VGA_BUFFER[row][col] = vga_c;

    VGA_COLUMN_POS++;
  }
}

#ifdef NFOS_DEBUG

#  ifndef KLEE_VERIFICATION

void nfos_vga_write_char(char c) { nfos_vga_write_byte((uint8_t)c); }

void nfos_vga_write_str(const char *s) {
  for (const char *p = s; *p; p++) {
    // Printable ASCII - isprint() technically doesn't exist in
    // freestanding C
    if (*p == '\n' || (*p >= ' ' && *p <= '~')) {
      nfos_vga_write_char(*p);
    } else {
      nfos_vga_write_byte(0xfe);
    }
  }
}

#  else // KLEE_VERIFICATION defined

#    include <stdlib.h>
#    include <klee/klee.h>

void nfos_vga_write_char(char c) {
  static char *out_buf = NULL;
  static size_t cap = 64;
  static size_t offset = 0;

  if (out_buf == NULL || offset >= cap) {
    cap *= 2;

    out_buf = realloc(out_buf, cap);
    klee_assert(out_buf != NULL);
  }

  if (c == '\n') {
    out_buf[offset] = '\0';
    klee_print_expr(out_buf, NULL);
    offset = 0;
  } else {
    out_buf[offset] = c;
    offset++;
  }
}

void nfos_vga_write_str(const char *s) { klee_print_expr(s, NULL); }

#  endif // KLEE_VERIFICATION

/* https://groups.google.com/forum/#!topic/comp.lang.c++.moderated/ihafayWmWU8
 */
void nfos_vga_write_int(int x) {
  if (x < 0) {
    nfos_vga_write_char('-');
    x = -x;
  }

  static char buf[32] = { 0 };

  int i = 30;

  for (; x && i; --i, x /= 10) {
    buf[i] = '0' + (x % 10);
  }

  nfos_vga_write_str(&buf[i + 1]);
}

#else // NFOS_DEBUG not defined, don't print anything

void nfos_vga_write_char(char c) {}
void nfos_vga_write_str(const char *s) {}
void nfos_vga_write_int(int x) {}

#endif // NFOS_DEBUG
