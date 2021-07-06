int glob() { 
  int * ii;
  ii = new int[4];
  return *ii;
}
class Base {
public:
  int _x;
};
class A : Base {
  void *operator new[](unsigned size);
  void m_fn2() { 
    Base* a = new A[3] ; }
};
class B {
  void *operator new[](unsigned size) { return (void*)(size+1); } 
  static bool nnnope(bool arg) { return !arg; }
         bool eeeyup(bool arg) { return !arg; }
  void bbb(unsigned int v) {B* bb = new B[v] ; }
};
