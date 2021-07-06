
int x = 2;

struct cls { 
	//@ requires x != 0; ensures x == 1 / \old(x);
	cls() { x = 1/x; }
};

cls obj;

int main(void) {
	cls();
	cls();
}

