#include "cstddef"

void* operator new(size_t t,void* p) { return p; }

void foo(void* p) {
	int* c = new(p)int;
}

