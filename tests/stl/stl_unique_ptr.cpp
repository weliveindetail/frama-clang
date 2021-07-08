/* run.config
OPT: @MACHDEP@ -deps -print
*/

#include <memory>

int test_primitive_payload(int var) {
  std::unique_ptr<int> up1(&var);
  std::unique_ptr<int> up2(new int);
  *up1 = var;
  *up2 = 2;
  std::swap(up1, up2);
  up1.reset();

  std::unique_ptr<int[]> up3(new int[2]);
  up3[0] = *up2; // var
  up3[1] = up3[0] + 1;

  int *up2_raw = up2.release();
  if (up2_raw != &var) {
    delete up2_raw; // unreachable
    return 0;
  }

  std::unique_ptr<int[]> up4 = std::move(up3);
  std::unique_ptr<int[]> up5 = std::forward<std::unique_ptr<int[]>>(up4);

  int *up5_raw =  up5.release();
  int result = up5_raw[0];
  delete[] up5_raw;

  return result;
}

struct PlainOldStruct {
  int val = 0;
  int pull() { return val; }
  void push(int x) { val = x; }
};

int test_struct_payload(int var) {
  PlainOldStruct pos;
  std::unique_ptr<PlainOldStruct> up1(&pos);
  std::unique_ptr<PlainOldStruct> up2(new PlainOldStruct);
  up1->push(var);
  up2->push(up1->pull() + 1);
  std::swap(up1, up2);
  up1.reset();

  std::unique_ptr<PlainOldStruct> up3 = std::move(up2);
  std::unique_ptr<PlainOldStruct> up4 =
      std::forward<std::unique_ptr<PlainOldStruct>>(up3);

  int result = up4->pull();
  PlainOldStruct *up4_raw = up4.release();
  if (up4_raw != &pos) {
    delete up4_raw; // unreachable
    return 0;
  }

  return result;
}

// Declaration before use.
template <typename T, int N = 0>
class ClassTemplate {
private:
  T val = N;
public:
  T *pull();
  void push(T *x);
};

// Use of declared ClassTemplate.
int test_template_payload(int var) {
  ClassTemplate<int> ct;
  std::unique_ptr<ClassTemplate<int>> up1(&ct);
  std::unique_ptr<ClassTemplate<int, 0>> up2(new ClassTemplate<int, 0>);
  up1->push(&var);
  std::swap(up1, up2);
  up1.reset();

  std::unique_ptr<ClassTemplate<int>> up3 = std::move(up2);
  std::unique_ptr<ClassTemplate<int>> up4 =
      std::forward<std::unique_ptr<ClassTemplate<int>>>(up3);

  int result = *up4->pull(); // var
  ClassTemplate<int> *up4_raw = up4.release();
  if (up4_raw != &ct) {
    delete up4_raw; // unreachable
    return 0;
  }

  return result;
}

// Definitions after use.
template <typename T, int N>
T *ClassTemplate<T, N>::pull() { return &val; }

template <typename T, int N>
void ClassTemplate<T, N>::push(T *x) { val = *x; }

// Driver loops through the input argc.
int main(int argc, char *argv[]) {
  int t1 = test_primitive_payload(argc);
  int t2 = test_struct_payload(t1);
  int t3 = test_template_payload(t2);
  return t3; // Expecting output: \result FROM argc
}
