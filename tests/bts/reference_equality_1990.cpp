
struct _pair { int xxx; };

//@ assigns \nothing; ensures \result == ppp.xxx;
int& fst(struct _pair& ppp) { return ppp.xxx; }

void bar(void) {
	struct _pair ppp;
	fst(ppp) = 222;
	//@ assert ppp.xxx == 222;
}
	
	
