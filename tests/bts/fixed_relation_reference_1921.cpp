/*@
  ensures \result >= x;
*/
int f(int& x) { return ++x; }

/*@
  ensures \result == x;
*/
int g(int& x) { return x; }

/*@
  ensures \result >= x;
*/
int h(int x) { return x; }
