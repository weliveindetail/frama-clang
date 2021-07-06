/* references and arithmetic operations */
int main () {
  int a = 0;
  int b = 1;
  int &y = a;
  int &z = b;
  z++;
  y = z;
  a++;
  if (a == 3 && b == 2) return 0;
  return 1;
};
