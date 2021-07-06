#include <atomic>

int main() {

  std::atomic<int> x = ATOMIC_VAR_INIT(5);
  x--;
  int y = 4;
  x.compare_exchange_strong(
    y, 6, std::memory_order_relaxed, std::memory_order_seq_cst);

  int a[5];
  std::atomic<int *>p = ATOMIC_VAR_INIT(&a[0]);
  p++;

  std::atomic_flag b = ATOMIC_FLAG_INIT;

  bool c = b.test_and_set();

  std::atomic<int> z;

  return x.load();
}
