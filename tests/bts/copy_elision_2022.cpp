
/*
	Return value optimization (RVO) test.
	The assertion in line 26 is provable,
	since Frama-C assumes absence of any RVO.
*/

int s = 1;

struct X {
	X(){}
	//@ requires 0 < s < 10000; assigns s; ensures s == \old(s)*10+2;
	X(const X& i) { s = s*10+2; }
};

X x;

//@ requires 0 < s < 1000; assigns s; ensures s == \old(s)*100+32;
X foo(void) {
	s = s*10+3;
	return x;
}

//@ requires 0 < s < 1000; assigns s; ensures s == \old(s)*100+32;
X bar(void) {
  X x;
  s = s * 10 + 3;
  return x;
}

int main(void) {
	X const k = foo();
	//@ assert s == 1322;
        s = 1;
        X const l = bar ();
        //@ assert s == 132;
}

