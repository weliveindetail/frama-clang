int glob() { 
  int * ii;
  ii = new int(10);
  return *ii;
}
class Base {
public:
  int _x;
};
class A : Base {
  void *operator new(unsigned size);
  void m_fn2() { 
    Base* a = new A ; }
};
class B {
  void *operator new(unsigned size) { return (void*)(size+1); } 
  static bool nnnope(bool arg) { return !arg; }
         bool eeeyup(bool arg) { return !arg; }
  void bbb() {B* bb = new B ; }
};
