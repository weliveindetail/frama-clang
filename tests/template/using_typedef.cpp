namespace foo {
template <typename T>
class Foo {
  T x; 
public:
  Foo(T _x): x(_x) { }
  T get() { return x; }
  void set(T i) { x = i; }
};
}

template <typename T> using Bar = foo::Foo<T>;

Bar<int> b = 1;

