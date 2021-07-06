// Logic functions in class scope but not static

class C {


public:
//@ logic int p(int i) = i;

//@ ensures \result == p(k);
int pos(int k) { return k; }

};


class A {

//@ ensures \result ==  c.p(k);
int m(C c, int k) { return c.pos(k); }

};
