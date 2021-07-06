// Logic functions in class scope and static

class C {


public:
//@ logic static int p(int i) = i;

//@ ensures \result == p(k);
static int pos(int k) { return k; }

};


class A {

//@ ensures \result ==  C::p(k);
int m(C c, int k) { return C::pos(k); }

};
