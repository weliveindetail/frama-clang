#include <utility>

struct S {
  int x;
  S(int y): x(y) { }
};

bool operator<(const S& x, const S& y) { return x.x < y.x; }

int f(int x) {
  int y = 2;
  std::swap<int>(x,y);
  int A[2] = { 1,2 };
  int B[2] = { 3,4 };
  std::swap<int,2>(A,B);
  int && z = std::forward<int>(x);
  int && t = std::forward<int>(z);
  int && u = std::move<int>(42);
  int && v = std::move_if_noexcept<int>(y);
  S s1(2);
  S s2(1);
  std::pair<int&, bool> ib (x,s1.x >=0);
  ib = std::make_pair(y, s2.x >= 0);
  std::pair<int,double> p;
  std::pair<int,double>q(8, 4.);
  std::pair<int,double>&r = q;
  std::swap<int,double>(p,r);
  int p1 = std::get<0,int,double>(p);
  double q2 = std::get<1,int,double>(q);
  if (std::rel_ops::operator><S>(s1,s2)) return 0; else return 1;
}
