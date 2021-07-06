/* translation of references */
int x = 0;
int &y = x;

int f () { y = 1; return x;};
