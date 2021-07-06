/*@ predicate is_normal_char(wchar_t c) = 0<=c<=255; */

/*@ predicate wchar_buff(wchar_t* p, integer l) = p[l] == L'\0'; */

int freq[256];

//@ requires is_normal_char(c);
void count(wchar_t c) { freq[c]++; }
