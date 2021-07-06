class A {
public:
  int f(void) { return 0; }
};

int g(void) { return 1; }

int main() {
  A a;
  int x = a.f();
  int y = g();
  return x;
}
