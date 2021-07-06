class A {
  int x;
public:
  A(): x(0) { }
  void foo(int y);
  void foo(int* y);
};

void A::foo (int y) { x += y; }

void A::foo(int* y)
{ (*y)++; x += *y; }

int main() {
  int y = 0;
  A a;
  a.foo(y);
  a.foo(&y);
  return 0;
}
