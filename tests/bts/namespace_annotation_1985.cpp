
namespace bar {
	int x = 3;
}

void foo(void) {
	//@ assert bar::x == 3;
}

