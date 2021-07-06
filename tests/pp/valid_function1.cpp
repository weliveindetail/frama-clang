
void f() {}

typedef void (*fp)();
int i;

//@ requires \valid_function(i); // ERROR
void h() {
}
