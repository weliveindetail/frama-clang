
int a,b,c,d;

/*@ requires d != a;
  @ behavior yyy:
  @   assumes i == 0;
  @   assigns b;
  @   assigns d \from a;
  @ behavior zzz:
  @   assumes i != 0;
  @   assigns d \from a;
  @   assigns b \from c;
  @*/
void f(int i) {}

