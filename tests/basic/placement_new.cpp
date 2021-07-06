#include <cstdlib>
#include<new>

class T
{
public:
    T() : x(42) {}
    int x;
};

class U {
  public:
  static int id;
  void* operator new(std::size_t s, int x) { 
    id = x; return malloc(s);
  }
  int foo;
  U(): foo(1) { }
};

int main()
{
    int t;
    void* p = &t;
    p = new(p) T;

    U* u = new (43) U();

    T obj;
    new(&obj) T;
    return obj.x + ((T*)p)->x + U::id + u->foo;
}
