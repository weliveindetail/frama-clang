int f(int x) {
  switch (x) {
    case 0: throw(0);
    case 1: throw(1.0);
    case 2: throw(2U);
    default: return 3;
  }
}

int g(int x) {
  int y = 0;
  try {
    y+=f(x);
    try {
      y+=f(y);
      return y;
    }
    catch (int z) { y+=z; return y; }
  }
  catch (unsigned z) { y+=z; return y; }
}

int main (int c, const char** foo) {
  try { return g(c); }
  catch (double d) { return 0; }
  catch (int z) { return 1; }
}
