struct foo {
  union {
    long l;
    int *p;
  };
};

int main () {
  int a = 0;
  foo f =  {{ .p=&a }};
  long y = f.l + 1;
  return 0;
}
