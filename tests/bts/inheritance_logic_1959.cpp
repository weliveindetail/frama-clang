
class A {
public:
	int a;
	//@ logic int lget_a() = a;

	//@ ensures \result == lget_a();
	int get_a(void) { return a; }
};

class B : public A {
public:
	//@ class invariant inv = (a == b == 1);
        //@ class invariant inv_this = (this->a == b);
        //@ class invariant inv2 = lget_a() == b;
        //@ class invariant inv_this2 = this->lget_a() == b;
	int b;
        //@ ensures a == 1 && this->a == 1;
	B() { a = b = 1; }
};

