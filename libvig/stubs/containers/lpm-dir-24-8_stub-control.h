#ifndef _LPM_DIR_24_8_STUB_CONTROL_H_INCLUDED_
#define _LPM_DIR_24_8_STUB_CONTROL_H_INCLUDED_

typedef bool lpm_entry_condition(uint32_t prefix, int value);

void lpm_set_entry_condition(struct lpm *lpm, lpm_entry_condition *cond);

#endif// _LPM_DIR_24_8_STUB_CONTROL_H_INCLUDED_
