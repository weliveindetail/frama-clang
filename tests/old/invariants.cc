class A {
  static int x;
  /*@ global invariant x_pos: x >= 0; */
public:
  typedef int INT;
  /*@ type invariant pos_INT(INT z) = z >= 0; */

  int y;
  /*@ class invariant y_val = this->y >= x; */

  A(): y(2) { }
};

int A::x = 0;

