#ifndef NFOS_SERIAL_H
#define NFOS_SERIAL_H

extern void nfos_serial_init(void);
extern void nfos_serial_write_char(char c);
extern void nfos_serial_write_str(const char *s);
extern void nfos_serial_write_int(int i);

#endif
