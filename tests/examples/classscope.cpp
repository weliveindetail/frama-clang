// Exhibits classes, but with logic functions outside of the class
// This example uses bool types

//@ logic boolean p(int i) = i > 0;
class C {


public:

//@ ensures CE: \result == p(k);
static bool pos(int k) { return k > 0; }

};


class A {

//@ ensures AE: \result ==  p(k);
bool m(int k) { return C::pos(k); }

};
