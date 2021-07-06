#include<array>
#include<iterator>

int main () {
  std::array<int, 4> A = { 0, 1, 2, 3};
  std::array<int, 2> B = { };

  int x = std::get<3,int,4>(A);
  B[1] = 42;
  B.at(0) = 36;
  {
    std::array<int, 4>::iterator it = A.begin();
    std::array<int, 4>::iterator end = A.end();
    for(; it < end; it++) (*it)++;
  }

  {
    std::array<int, 2>::const_reverse_iterator it = B.crbegin();
    std::array<int, 2>::const_reverse_iterator end = B.crend();
    int res = 0;
    for(; it < end; it++) res+= *it;
  }

  return 0;
}
