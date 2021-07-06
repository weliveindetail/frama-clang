class A {

private: int v;

public:
  //@ predicate P() = \this.v == 0;

  //@ class invariant Pos = \this.v >= 0;

  A(): v(1) { }

  //@ behavior default: ensures this->P();
  int f() {
    v = 0;
    return v;
  }

};

int main () {

  A a;

  a.f();
  //@ assert a.P();

  return 0;
}
