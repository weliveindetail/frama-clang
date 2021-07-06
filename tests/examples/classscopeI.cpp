// logic function declared outside of a class
// uses int instead of bool type

//@ logic int p(int i) = i;
class C {


public:

//@ ensures \result == p(k);
static int pos(int k) { return k; }

};


class A {

//@ ensures \result ==  p(k);
int m(int k) { return C::pos(k); }

};
