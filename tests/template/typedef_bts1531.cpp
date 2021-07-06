
template<typename T> class foo {
public:
  typedef T bar;
};

int f(foo<int>::bar x) { return x; }
