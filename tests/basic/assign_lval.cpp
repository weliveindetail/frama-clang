#if 1
int y;
int f(int *p) {
  return *p;
}
#endif 

void g(int &x)
{
  x++;
}

int main()
{
  int x=55;
  g((x+=1337));
  g(++x);
 #if 1
  y=x;
  f(&(x+=1));
  return f(&(x=42));
#endif
}
