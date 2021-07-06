
struct X { bool a; };

struct Ptr { X* operator->(); };

//@ requires p->a;
void foo(Ptr p);

int main(void) {
	Ptr p;
	//@ assert &p->a == 0;
}

