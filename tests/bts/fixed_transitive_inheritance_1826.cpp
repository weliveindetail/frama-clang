struct A {
	int i;
	void foo () {}
};
struct B : A {
};
struct C : B {
	void bar () {foo();}
	void baz () {i = 5;}
};
