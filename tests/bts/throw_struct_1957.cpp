
struct Ex {
	//int ex;
};

void foo(void) {
	//throw new Ex;
	throw 3;
}

int main(void) {
	try {
		//foo();
	}
	catch (Ex e) {
	}
}

