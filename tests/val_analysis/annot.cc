class A {
  int x;
public:
  A(): x(1) { }
  /*@ logic int foo() reads x; */

  /*@ class invariant val_foo = \this.x == foo(); */

  /*@ behavior default: ensures \result == foo(); */
  int get_x() { return x; }

};

int main () {
  A a;
  int y = a.get_x();
  /*@ assert y == a.foo(); */
  return 0;
}
