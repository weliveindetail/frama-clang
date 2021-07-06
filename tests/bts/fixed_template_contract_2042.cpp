
template<class T> int foo (T    a) { return 1; }

//@ ensures \result == 4;
template<       > int foo (int  a) { return 2; }

//@ assigns \nothing; ensures \result == 4;
template<       > int foo (char a) { return 3; }

int bar(void)                      { return 4; }

