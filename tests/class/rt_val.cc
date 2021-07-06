/* function returning an object */

struct Foo {
  int x;
  Foo(int _x) { x = _x;}
};

Foo f(int y) { return (Foo (y+y));}

int g () {
  Foo z = f(1);
  return z.x;
}
