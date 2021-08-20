struct UliEUc3capiE_0 {
  int *__fc_lambda_overload_0(struct UliEUc3capiE_0 const *, int) /*@
    ghost () */
      ;
  int cap;
};
void UliEUc3capiE_0_init_captures(
    __declspec(
        __fc_initialized_object) struct UliEUc3capiE_0 const *__fc_closure,
    int cap) /*@
ghost () */
{
  __fc_closure->cap = cap;
}
void UliEUc3capiE_0_init_0(
    __declspec(
        __fc_initialized_object) struct UliEUc3capiE_0 const *__fc_closure,
    int *__fc_func(struct UliEUc3capiE_0 const *, int) /*@ ghost () */) /*@
    ghost () */
{
  __fc_closure->__fc_lambda_overload_0 = __fc_func;
}
int UliEUc3capiE_0_body_0(struct UliEUc3capiE_0 const *__fc_closure,
                          int val) /*@ ghost () */
{
  return __fc_closure->cap - val;
}
int _Z17test_cxx11_lambdaii(int cap, int i) /*@ ghost () */
{
  struct UliEUc3capiE_0 lam1;
  ;
  const struct UliEUc3capiE_0 __fc_lambda_tmp;
  ;
  UliEUc3capiE_0_init_captures(&__fc_lambda_tmp, cap) /*@ ghost ( ) */;
  ;
  UliEUc3capiE_0_init_0(&__fc_lambda_tmp, UliEUc3capiE_0_body_0) /*@
 ghost ( ) */
      ;
  ;
  lam1 = __fc_lambda_tmp;
  return (lam1.__fc_lambda_overload_0)(&lam1, i) /*@ ghost ( ) */;
}
struct UliEUc3capiE_1 {
  int *__fc_lambda_overload_1(struct UliEUc3capiE_1 const *, int) /*@
    ghost () */
      ;
  int cap;
};
void UliEUc3capiE_1_init_captures(
    __declspec(
        __fc_initialized_object) struct UliEUc3capiE_1 const *__fc_closure,
    int cap) /*@
ghost () */
{
  __fc_closure->cap = cap;
}
void UliEUc3capiE_1_init_1(
    __declspec(
        __fc_initialized_object) struct UliEUc3capiE_1 const *__fc_closure,
    int *__fc_func(struct UliEUc3capiE_1 const *, int) /*@ ghost () */) /*@
    ghost () */
{
  __fc_closure->__fc_lambda_overload_1 = __fc_func;
}
int UliEUc3capiE_1_body_1(struct UliEUc3capiE_1 const *__fc_closure,
                          int val) /*@ ghost () */
{
  return __fc_closure->cap - val;
}
int _Z22test_cxx14_single_instii(int cap, int i) /*@ ghost () */
{
  struct UliEUc3capiE_1 lam2;
  ;
  const struct UliEUc3capiE_1 __fc_lambda_tmp_0;
  ;
  UliEUc3capiE_1_init_captures(&__fc_lambda_tmp_0, cap) /*@ ghost ( ) */;
  ;
  UliEUc3capiE_1_init_1(&__fc_lambda_tmp_0, UliEUc3capiE_1_body_1) /*@
 ghost ( ) */
      ;
  ;
  lam2 = __fc_lambda_tmp_0;
  return (lam2.__fc_lambda_overload_1)(&lam2, i) /*@ ghost ( ) */;
}
struct UlifEUc3capiE_2 {
  int *__fc_lambda_overload_3(struct UlifEUc3capiE_2 const *, int) /*@
    ghost () */
      ;
  float *__fc_lambda_overload_2(struct UlifEUc3capiE_2 const *, float) /*@
      ghost () */
      ;
  int cap;
};
void UlifEUc3capiE_2_init_captures(
    __declspec(
        __fc_initialized_object) struct UlifEUc3capiE_2 const *__fc_closure,
    int cap) /*@
ghost () */
{
  __fc_closure->cap = cap;
}
void UlifEUc3capiE_2_init_3(
    __declspec(
        __fc_initialized_object) struct UlifEUc3capiE_2 const *__fc_closure,
    int *__fc_func(struct UlifEUc3capiE_2 const *, int) /*@ ghost () */) /*@
    ghost () */
{
  __fc_closure->__fc_lambda_overload_3 = __fc_func;
}
int UlifEUc3capiE_2_body_3(struct UlifEUc3capiE_2 const *__fc_closure,
                           int val) /*@ ghost () */
{
  return __fc_closure->cap - val;
}
void UlifEUc3capiE_2_init_2(
    __declspec(
        __fc_initialized_object) struct UlifEUc3capiE_2 const *__fc_closure,
    float *__fc_func(struct UlifEUc3capiE_2 const *, float) /*@ ghost () */) /*@
      ghost () */
{
  __fc_closure->__fc_lambda_overload_2 = __fc_func;
}
float UlifEUc3capiE_2_body_2(struct UlifEUc3capiE_2 const *__fc_closure,
                             float val) /*@ ghost () */
{
  return (float)__fc_closure->cap - val;
}
int _Z21test_cxx14_multi_instiif(int cap, int i, float f) /*@ ghost () */
{
  struct UlifEUc3capiE_2 lam3;
  ;
  const struct UlifEUc3capiE_2 __fc_lambda_tmp_1;
  ;
  UlifEUc3capiE_2_init_captures(&__fc_lambda_tmp_1, cap) /*@ ghost (
) */;
  ;
  UlifEUc3capiE_2_init_3(&__fc_lambda_tmp_1, UlifEUc3capiE_2_body_3) /*@
 ghost ( ) */
      ;
  ;
  UlifEUc3capiE_2_init_2(&__fc_lambda_tmp_1, UlifEUc3capiE_2_body_2) /*@
 ghost ( ) */
      ;
  ;
  lam3 = __fc_lambda_tmp_1;
  int addend = 1;
  if ((lam3.__fc_lambda_overload_2)(&lam3, f) /*@ ghost ( ) */ < 0.5)
    addend = 0;
  return (lam3.__fc_lambda_overload_3)(&lam3, i) /*@ ghost ( ) */ + addend;
}
int main(int argc, char *argv[]) /*@ ghost () */
{
  int res1 = _Z17test_cxx11_lambdaii(argc, argc) /*@ ghost ( ) */;
  int res2 = _Z22test_cxx14_single_instii(argc, argc) /*@ ghost ( ) */;
  int res3 = _Z21test_cxx14_multi_instiif(argc, argc, (float)argc) /*@
    ghost ( ) */
      ;
  return (res1 + res2) + res3;
}