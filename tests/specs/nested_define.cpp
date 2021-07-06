#define BAR (1)
#define FOO BAR

//@ ensures \result == BAR;
int bar() { return BAR; }

//@ ensures \result == FOO;
int foo () { return FOO; }
