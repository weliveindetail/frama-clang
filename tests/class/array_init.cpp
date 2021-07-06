struct A {
int x;
int y;
A(int _x = 32, int _y = 46): x(_x), y(_y) { }
};

A a0[2];

A a1[2] = { A(6,13), A(25) };

int main() {
  return a0[0].x + a1[0].y + a1[1].x;
}
