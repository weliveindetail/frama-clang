
int test_cxx14_multi_inst(int cap, int i, float f) {
  auto lam3 = [cap](auto val) { return cap - val; };
  int addend = 1;
  if (lam3(f) < .5f)
    addend = 0;
  return lam3(i) + addend;
}
