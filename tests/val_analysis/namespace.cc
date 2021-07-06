class A {
  class B { public: int x;
    ///*@ requires this->x == 2; */ ~B() { };
  };
public:
  int f (B);
  B g();
  //~A() { return; };
};

int A::f(B x) { return x.x; }

A::B A::g () { B x; x.x = 2; return x;}

int main () {
  A a;
  int x = a.f(a.g());
  /*@ assert x == 2; */
  return x;
}
