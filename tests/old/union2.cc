int f () {
  union { int i; void * p; };
  int a = 0;
  p = &a;
  return i; // returns the address of a as an int
}
