template<class T> class foo {
  T* x;
public:
  foo(T* _x) { x = _x;}
  T* get_x () { return x;}
  void set_x(T* _x) { x = _x;}
};

class bar {
  int y;
public:
  int z;
  bar() { y = 0; z =0;}
  int get_y() {return y;}
  void incr() { y++;}
};

int main() {
  bar b;
  foo<bar> f(&b);
  int z = f.get_x()->z;
  return 0;
}
