
struct iterator { };

int current;

//@ ensures current == \old(current) + 11;
void foo() {
	iterator tmp;
	current = current + 11;
}

