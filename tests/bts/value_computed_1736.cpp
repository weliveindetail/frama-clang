
class Point2 {
public:
	int x;
	int y;
	Point2() : x(), y(1) {}
};

int main(void) {
	Point2 p;
        long long foo = *((long long*)&p);
        return *((short*)((char*)&p.x+3));
}

