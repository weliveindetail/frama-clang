
class foo {
public:
	foo() { }
	void cat(foo x) { }
};

int main() {
	foo f;
	f.cat(f);
}

