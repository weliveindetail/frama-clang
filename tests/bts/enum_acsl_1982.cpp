
enum _e { a = 4, b = 9 };

//@ ensures \forall enum _e i; \result != i;
int foo(void);

