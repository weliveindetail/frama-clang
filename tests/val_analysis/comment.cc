/* How do we treat comment and annotations in C++ ? */

class Point {
public:
  int get_x () { return _x; };
  int get_y () { return _y; };
  Point (int x = 0, int y = 0) { _x = x; _y = y; };

  /*@ requires (dx != 0); */
  void move_x (int dx) { _x += dx; };

  /*@ requires (dy != 0); */
  void move_y (int dy) { _y += dy; };

  void move(int dx , int dy) { this -> move_x(dx); this -> move_y(dy);};
private:
  int _x;
  int _y;
};

int main () {
  Point o;
  o.move_x(1);
  o.move_y(0); //boo...
  /*@ assert (o._x == 1 && o._y == 0); */
  return 0;
}
