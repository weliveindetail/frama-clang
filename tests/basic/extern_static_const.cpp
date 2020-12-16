/* run.config
   OPT: @MACHDEP@ @CXX@ -check -print -cxx-keep-mangling
*/

extern "C" {
  int f(int);
  const int X = 42;
  int g(int);
  struct C { int x; };
  struct C c = { 1 };
  static const int Z = 23;
  extern const int A = 54;
};

extern "C" const int Y = 43;

int h(int);

int main () { return h(f(X) + g(Y) + c.x + Z + A); }
