// use of default arguments
int f (int x = 0) { return (x + x);};

struct Foo {
  int x;
  Foo(int a=0): x(a) {};
};

int main () {
  Foo x;
  Foo y(1);
  if (f(x.x) != f()) return 1;
  return 0;
};
