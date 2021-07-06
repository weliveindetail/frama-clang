/* run.config
OPT: @CXX@ @EVA@ -print
*/

struct A {
  int x;
  int y;
  A(int _x, int _y=1): x(_x),y(_y) { }
  
};

struct B {
  int x;
  int y;
};

A a[2] = { 2, 4 }; // a[0] == A(2,1); a[1] == A(4,1);

B b[2] = { {7}, {14} }; // b[0].x == 7; b[0].y == 0; b[1].x == 14; b[1].y == 0; 

B b1[2] = { { 28,43 } };
// b1[0].x == 28; b1[0].y == 43; b1[1].x == 0; b1[1].y == 0;

int main () { return a[1].x + b[1].x + b1[0].y; } // returns 61
