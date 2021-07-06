struct A;
struct B { A* a; };
struct A { int x; };

int f (B& x) { return x.a->x; }
