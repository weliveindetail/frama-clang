
void f() {}

typedef void (*fp)();
int i;

void g(fp ff) {
//@ assert \valid_function{Pre}(ff);
}
