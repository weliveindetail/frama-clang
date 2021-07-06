// testing namespace resolution with two classes.

class A {
public:
  int x;
};

class B {
public:
  int foo (A x) { return x.x; };
};
