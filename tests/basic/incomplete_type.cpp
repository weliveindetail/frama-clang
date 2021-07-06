class A {
public:
  enum { E, F } t;
};
class B {
  int a;
  A mem[];
public:
  void m_fn1(A *&, long, unsigned);
};

void B::m_fn1(A *&p1, long, unsigned) {
  p1->t = A::E;
  mem[0].t = A::F;
}

int main() {
  B b;
  A a;
  A* p = &a;

  b.m_fn1(p,0,0);

  return a.t;

}
