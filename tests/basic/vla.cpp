typedef long Paddr;
class A {
  void m_fn1(Paddr, unsigned) const;
};
void A::m_fn1(Paddr, unsigned) const {
  long count;
  Paddr table[count];
}
