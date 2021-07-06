#include <memory>

int main() {
  int * x = new int();
  *x = 42;
  int *y = new int ();
  *y = 36;
  std::auto_ptr<int> p(x);
  std::auto_ptr<int> q(p);
  p.reset(y);
  int a =  *p + *q.release();

  std::unique_ptr<int> up(new int);
  *up =1;
  std::unique_ptr<int> up1(new int);
  *up1 = 2;
  std::swap(up, up1);

  up1.reset();

  std::unique_ptr<int []> ua(new int [2]);

  ua[1] = 3;

  std::unique_ptr<int []>ua1(std::forward<std::unique_ptr<int[]>>(ua));

  ua1[0] = 4;

  int z = ua1[1];

  ua = std::forward<std::unique_ptr<int[]>>(ua1);

  int *t =  ua.release();

  return t[1];
}
