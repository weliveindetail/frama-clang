/* passing references to functions */
void f (int &x) { x = 42; };

int main () {
  int x = 0;
  int &y = x;
  f(y);
  if ( x == y ) {return 0;} else {return 1;};
};
