/* various uses of constructor */
struct Foo {
  int x;
  Foo (int a = 0) { x = a;};
};

Foo x;
Foo y(1);

int main () {
  x = Foo (2);
  return 0;
};

