
class Point {
	~Point() { } 
	void foo(Point p) { } 
	void bar(Point p) { foo(p); }
}; 


