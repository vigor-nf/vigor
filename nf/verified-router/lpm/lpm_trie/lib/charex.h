/*@
fixpoint char char_of_uchar(unsigned char c);

fixpoint unsigned char uchar_of_char(char c);

lemma_auto void map_uchar_of_char_char_of_uchar(list<unsigned char> ucs);
    requires true;
    ensures map(uchar_of_char, map(char_of_uchar, ucs)) == ucs;

lemma_auto void map_char_of_uchar_uchar_of_char(list<char> cs);
    requires true;
    ensures map(char_of_uchar, map(uchar_of_char, cs)) == cs;

lemma_auto void chars_to_uchars(void *p);
    requires [?f]chars(p, ?n, ?cs);
    ensures [f]uchars(p, n, map(uchar_of_char, cs));

lemma_auto void uchars_to_chars(void *p);
    requires [?f]uchars(p, ?n, ?ucs);
    ensures [f]chars(p, n, map(char_of_uchar, ucs));
@*/
