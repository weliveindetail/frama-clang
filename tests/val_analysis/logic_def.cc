struct X {
  int x;
  //@ logic int foo() = \this.x;
  X(): x(42) { }
};

int main() {
  X x;
  //@ assert x.foo() == 42;
  return 0;
}
