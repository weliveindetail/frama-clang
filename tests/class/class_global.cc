/* global instances of classes + references */
class Bar { public: int t; Bar (int x) { t = x + x;};};
class Foo {
public: 
  int x;
  Bar y;
  Foo (): x(0), y(1) { x = 42; y.t = 36; };
};

Foo foo;

Foo &bar = foo;

Foo const & baz = Foo();

int main () {
  foo.x = 1;
  foo.y.t = 0;
  if (bar.x == baz.x) return foo.y.t; else return 1;
};
