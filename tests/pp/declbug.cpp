// This checks for the following problem. If there is no declaration of 
// struct x, then clang inserts a generated declaration just prior to the
// function declaration. Then the ACSL comment tries to attach to the 
// struct declaration instead of the function declaration, and fails with
// obscure information.
//struct x;
/*@
requires \true;
*/
extern int f(struct x *y);

