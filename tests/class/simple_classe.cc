// simple class definition. No inheritance, no virtual meth
// covers quite a lot of fiasco code...

class Point {
public:
  Point () { _x =0; _y=0;}
  Point (int x, int y);
  // Point (const Point& p);
  void move_x (int);
  void move_y (int);
  void move (int, int);
  int get_x () { return _x;}
  int get_y () { return _y;}
private:
  int _x;
  int _y;
};

Point::Point (int x, int y) { _x = x; _y = y;}

//Point::Point(const Point& p) { _x = p._x; _y = p._y; }

void Point::move_x(int dx) { _x += dx;}
void Point::move_y(int dy) { _y += dy;}

void Point::move(int dx, int dy)
{ this->move_x(dx); this->move_y(dy); };

int main () {
  Point o;
  Point a(1,1);
  Point b(a);
  Point *c = &a;
  a.move(1,-1);
  c->move_x(0);
  return 0;
}
