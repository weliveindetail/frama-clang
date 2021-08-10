#include <ratio>

int main(int argc, char *argv[]) {
  using one_third = std::ratio<1, 3>;
  using two_fourths = std::ratio<2, 4>;
  using five_sixth = std::ratio_add<one_third, two_fourths>;
  return (std::kilo::num - five_sixth::num - five_sixth::den + argc == 990) ? 0 : 1;
}
