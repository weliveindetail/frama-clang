/* run.config
   OPT: @CXX@ -check -print
*/

int f(int x) { if (x < 0) throw(5); else if (x > 0) throw(5.0); return 2; }

int g(int x) {
  try { f(x); return 0; }
  catch (int x) { return 1; }
}
