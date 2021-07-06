union A {
  int x;
  char y;
};

int f(A a) { return a.x; }

int main() {
  A a;
  a.x = 42;
  int b = f(a);
  //@assert b == 42;
  return 0;
}
