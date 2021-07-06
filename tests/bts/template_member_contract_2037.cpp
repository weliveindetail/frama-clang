
template<class T> struct List;

template<class T> struct List<T*> {
	//@ assigns \nothing;
	static int foo(void);
};

int main(void) {
	List<int*>::foo();
}

