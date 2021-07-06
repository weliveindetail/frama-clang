union foo {
  int i;
  void *p;
  int as_int_pointer();
};

int foo::as_int_pointer () {
  return *(int *)p;
}
