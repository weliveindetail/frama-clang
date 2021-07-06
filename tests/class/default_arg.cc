/* default argument given by a constructor */

struct Foo {
  int x;
  Foo () { x = 0; };
  void inc () { x++; };
};

int f (Foo x = Foo()) { return x.x; };

int main () {
  int x = f();
  Foo z;
  z.inc(); 
  int y = f(z);
  if (y == 1 && x == 0) return 0;
  return 1;
}
