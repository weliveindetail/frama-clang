int main () {
  int x = 3;
  auto lam = [&] (int y) { x+=y; };
  lam(1);
  return x;
};
