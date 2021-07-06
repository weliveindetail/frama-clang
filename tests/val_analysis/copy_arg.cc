struct Foo {
  int x;
  Foo() { x = 0;}
  Foo(Foo& src) {
    x = src.x++;
  }
  Foo& operator = (Foo& src) {
    x = src.x;
    return *this;
  }
};

Foo f(Foo x) { return x; }

int main() {
  Foo x;
  Foo y;
  f(x);
  y = x;
  return 0;
}
