
int x = 1;

class Point {
public:
	~Point() { x = 1/0;} 
}; 

void foo(void) {
	Point p;
}

int main(void) {
	foo();
	return x+2;
}

