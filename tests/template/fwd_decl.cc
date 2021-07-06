template<typename T> T* id(T* x) { return x; }

struct A { int x; };

int main ()
{
  A a;
  A* b = id<A>(&a);
  return 0;
}
