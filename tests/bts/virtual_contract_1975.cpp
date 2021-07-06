
class Rectangle {
public:
	//@ assigns \nothing; ensures \result == 111;
        virtual int area() const { return 111; }
};

class Square : public Rectangle {
public:
	//@ assigns \nothing; ensures \result == 222;
        virtual int area() const { return 222; }
};

int main() {
    Square s;

    Rectangle* rp = &s;
    int const a = rp->area();
    //@ assert a == 333;
}

