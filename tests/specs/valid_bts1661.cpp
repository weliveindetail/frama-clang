
//@ requires \valid(p);
void foo(int *p) {}

void bar() {
	foo((int*)0);
}

