#ifndef DSOS_SERIAL_H
#define DSOS_SERIAL_H

extern void dsos_serial_init(void);
extern void dsos_serial_write_char(char c);
extern void dsos_serial_write_str(const char *s);
extern void dsos_serial_write_int(int i);

#endif
