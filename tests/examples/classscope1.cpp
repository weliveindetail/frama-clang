// Exhibits static logic functions and class qualifiers on the name

class C {


public:
//@ logic static boolean p(int i) = i > 0;

//@ ensures \result == p(k);
static bool pos(int k) { return k > 0; }

};


class A {

//@ ensures \result ==  C::p(k);
bool m(int k) { return C::pos(k); }

};
