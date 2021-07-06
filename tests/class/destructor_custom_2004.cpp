
struct cls {
	~cls() { }
	bool test() { return true; }
};

int main(void) {
	if (cls().test())
		;
}

