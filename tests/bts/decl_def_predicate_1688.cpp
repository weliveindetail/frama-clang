
//@ predicate foo(int l);
//@ predicate foo(int l) = (42==42);

//@ ensures foo(l);
void insert(int l) { }

