// predefined variables bearing function names
int f () {
  int x = 0;
  const char* t = __func__;
  const char* u = __FUNCTION__;
  const char* v = __PRETTY_FUNCTION__;
  return x;
};
