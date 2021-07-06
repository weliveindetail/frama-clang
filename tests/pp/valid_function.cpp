
void f() {}

typedef void (*fp)();
int i;

//@ requires \valid_function(ff);
void g(fp ff) {
}
