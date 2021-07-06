struct A {
  int f() { z.x++; return z.y;}
  A() { z.x = 0; z.y = 1; };
  struct B { int x; int y;} z;
};

int main () {
  A a;
  return a.f();
}
