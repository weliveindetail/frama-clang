
static int s;

//typedef int T;

//@ requires s>0; assigns s; ensures s*2 == 2;
template<class T>
                  void nop(T t) { s = 1; }

int main() {
  s = 1;
  nop(4);
  //@ assert s == 1;
}

