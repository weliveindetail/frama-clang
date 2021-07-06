
struct X {
	int x;
	//@ ensures x * 10 == 130;
	X() { x = 13; }

        // contract should be automatically generated...
        // @ assigns x; ensures x == src.x;
        // X(const X& src) { x = src.x; }
};

//@ requires i.x <= 42;
void foo(X i) { }

int main() {
	X i;
	//@ assert i.x <= 42;
	foo(i);
}

