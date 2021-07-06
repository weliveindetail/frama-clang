#include "assert.h"

struct A { virtual void bar(void){ } }; 
struct B { virtual void bar(void){ } };

int main(void) {
	A aaa;
	B* const bp = dynamic_cast<B*>(&aaa);
	//@ assert bp!=0;
	assert(bp!=0);
}

