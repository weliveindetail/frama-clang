struct A {
  A() { raw = 1; }
  union {
    int raw;
    struct {
      int x: 8;
      int y: 8;
      int zero: 16;
    } view;
  };
};

int f(A a) {
  return a.raw;
}

int main() {
  A ma;
  int b = f(ma);
  //@assert b == 1;
  return 0;
}
