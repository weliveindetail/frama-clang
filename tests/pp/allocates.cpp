int* x;
int* y;
/*@


assigns x;
frees x;
allocates \result;
behavior bb:
  assigns \nothing;
  frees \nothing;
  allocates \nothing;
*/
int* m() { return x; }
