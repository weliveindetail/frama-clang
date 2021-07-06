
struct X { int a; };

X x;

struct Ptr {
	//@ assigns \nothing; ensures \result == &x;
	X* operator->() { return &x; }
};

int main(void) {
	Ptr p;
	p->a = 3;
	//@ assert p->a == 3;
}

