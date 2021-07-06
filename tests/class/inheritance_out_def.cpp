class A {
  public:
  int x;
  virtual int get_sum() { return x; }
};

class B: public A {
  public:
  int y;
  B();
  virtual int get_sum() { return x + y; }
};

B::B(): A(), y(4) { x = 2; }

int main() {
  B b;
  return b.get_sum();
}

