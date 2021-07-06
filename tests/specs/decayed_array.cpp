/*@ requires \exists integer i; 0<=i<n ==> p[i] != 0; */
int* f(int n, int p[]) { while(*p) p++; return p; } 
