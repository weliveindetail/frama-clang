
static int last = 13;

class Clss {
public:
	/*@
		assigns last;
		ensures last * 2 == 84;		// force alt-ergo call
	*/
	~Clss() { last = 42; }
};

int main(void) {
	{
		Clss inst;
		//inst.~Clss();
	}
	//@ assert last == 42;
}

