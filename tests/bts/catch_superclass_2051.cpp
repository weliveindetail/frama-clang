
class Matherr {};
class Underflow: public Matherr {};

void foo(void) {
	try {
	}
	catch (Matherr) {
	}
}

