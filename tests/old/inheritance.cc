/* run.config
DONTRUN: under development
*/

class A {
protected:
     int x;
public:
     A() { x = 0; }
     A(int x) { this -> x = x; }
     int get_x() { return x; }
     virtual void move(int dx) { x+=dx; }
};

class C {
protected:
     int z;
public:
     C() { z = 0; }
     C(int x) { this -> z = x; }
     int get_z() { return z; }
     virtual void move(int dx) { z+=dx; }
};

class B: virtual A, virtual C { 
     int y;
public:
     B(): A() { y = 0; }
     B(int x, int y): A(x) { this->y = y; }
     int get_y() { return y; }
     virtual void move(int d) { x+=d; y+=d; }
};
