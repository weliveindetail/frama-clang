
class Point2
{
    int x;
    //@ assigns this->x;
    Point2(const Point2& p) { x = p.x; }
    
  //@ assigns x;
  Point2()  { x = 0; }
};

