struct S { int i; };
void foo (S* s) {
	//@ assert s->i == s->i == s->i;
        //@ assert s->i == s->i && s->i == s->i;
}
