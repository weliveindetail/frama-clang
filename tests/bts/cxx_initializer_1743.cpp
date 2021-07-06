
int g;

class list {
public:
	int* n;
	list() : n(new int) {
		//n = new int;
		g = *n;
	}
};

int main() { list l; }


