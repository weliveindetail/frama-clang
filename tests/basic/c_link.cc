struct Foo {
  int x;
};

struct Bar { int y; int z;};

extern "C" Foo f(Bar);

int main() {
  Foo g;
  Bar b;
  Foo x = f(b);
  g = f(b);
  return 0;
}
