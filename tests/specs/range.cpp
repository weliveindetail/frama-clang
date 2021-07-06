int x[512];

/*@ requires \subset(p, x+(0..)); */
int foo(int *p) { return *p; }
