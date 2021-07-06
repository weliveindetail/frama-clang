int  v = 7;
int& r = v;
int& foo() { return r; }
void bar() { foo() = 4; } 
