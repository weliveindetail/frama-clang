class A {
private:
  static int x;
  static int f() { return 3; }
};

int A::x = f();

