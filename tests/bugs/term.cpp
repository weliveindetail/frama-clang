/*@
behavior c:
requires \true;
terminates \true; // ERROR
ensures \true;
*/
void m1() {}

/*@
requires \true;
terminates \true; // OK
ensures \true;
*/
void m2() {}

/*@
terminates \true; //OK
behavior c:
requires \true;
ensures \true;
*/
void m3() {}

/*@
requires \true;
terminates \true; //OK
behavior c:
requires \true;
ensures \true;
*/
void m3a() {}

/*@
terminates \true; //ERROR
requires \true;
behavior c:
requires \true;
ensures \true;
*/
void m3b() {}

/*@
terminates \true;
terminates \true; // ERROR
behavior c:
requires \true;
ensures \true;
*/
void m4() {}

