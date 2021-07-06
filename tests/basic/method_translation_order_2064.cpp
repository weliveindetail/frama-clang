
class Point
{
      void bar   (Point& p) { xx=p.xx;  }
      void foo   (Point& p) { xx=p.x(); }
      Point(Point& p)       :  xx(p.xx) {}
      Point(const Point& p) : xx(p.x()) {}

    int x() const { return xx; }

    int xx;
};

