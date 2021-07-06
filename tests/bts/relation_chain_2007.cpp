
struct X {};

//@ requires 0 < x < 9;
void foo(X x) {}

//@ requires 0 < x;
void bar(X x) {}
