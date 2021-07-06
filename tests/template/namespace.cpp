namespace foo {
  template <typename T> struct bar { T x; };
  struct baz { int y; };
}

int main () {
  foo::bar<int>a;
  foo::baz b;
  return a.x + b.y;
}
