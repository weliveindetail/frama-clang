
class cl {
	mutable int x;
public:
	//@ assigns x;
	void foo(void) const { x = 0; }
};

//@ assigns c.x;
void bar(cl& c) {
	c.foo();
}

