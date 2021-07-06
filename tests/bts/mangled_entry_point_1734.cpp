// Cannot have a constructor as entry point
class Point2
{
    int x;
    Point2() : x() {}
    int get() {return x; }
};

int mymain(void) {
	return 0;
}

template <typename T> class Foo {
  T x;
  T get() { return x; }
};

Foo<int> x;
