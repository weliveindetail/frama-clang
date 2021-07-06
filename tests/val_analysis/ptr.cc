static int x = 0;

class A {
  int* y;
public:
  int* f();
  A() { y = &x; }
};

int* A::f() { return y; }

int main() {
  A a;
  *a.f() = 2;
  return 0;
}
