struct A {
  friend int f(void);
  int g();
  int x;
};

A a;

int f();

int main() {
  int x = f();
  return 0;
}

int A::g() { return x; }

int f () { return 0;}
