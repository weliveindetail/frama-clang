/* run.config
OPT: @MACHDEP@ -deps -cpp-extra-args="-std=c++14" -print
*/

int test_cxx11_lambda(int cap, int i) {
  auto lam1 = [cap] (long val) { return cap - val; };
  return lam1(i);
}

int test_cxx14_single_inst(int cap, int i) {
  auto lam2 = [cap](auto val) { return cap - val; };
  auto lam2b = [cap](auto val) { return cap - val; };
  return lam2(i) + lam2b(i);
}

int test_cxx14_multi_inst(int cap, int i, float f) {
  auto lam3 = [cap](auto val) { return cap - val; };
  int addend = 1;
  if (lam3(f) < .5f)
    addend = 0;
  return lam3(i) + addend;
}

// We know argc will be 1, but the compiler doesn't know it.
int main(int argc, char *argv[]) {
  int res1 = test_cxx11_lambda(argc, argc);
  int res2 = test_cxx14_single_inst(argc, argc);
  int res3 = test_cxx14_multi_inst(argc, argc, static_cast<float>(argc));
  return res1 + res2 + res3;
};
