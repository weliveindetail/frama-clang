/* run.config
   OPT: @CXX@ -check -print
*/


int f(int x) { throw(5.0); }

int g(int x) {
  try {
    f(x);
    return 0;
  }
  catch (...)
    { throw; }
  return 1;
}


int h(int x) {
  try {
    f(x);
    return 0;
  }
  catch (double x)
    { throw; }
  return 1;
}

int k(int x) {
  try {
    f(x);
    return 0;
  }
  catch (int x)
    { throw; }
  return 1;
}


