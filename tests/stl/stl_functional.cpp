#include <functional>

typedef std::reference_wrapper<int(*)(int)> foo;

typename foo::result_type x = 5;

typedef std::reference_wrapper<int> bar;

typename bar::type y = 42;

int f(int x) { return x; };

int (*pf)(int) = f;

auto wrap_f = std::ref(pf);

int t = wrap_f(5);
int u = wrap_f(std::forward<int>(x));

int h(const int& x, const int& y) { return x * y; }

int g(int c) {
  std::function<int(const int&,const int&)> op(h);
  std::less<int> test;
  if (test(c,0)) { op = std::minus<int>(); }
  else if (c > 0) { op = std::plus<int>(); }
  return op(5,4);
}
