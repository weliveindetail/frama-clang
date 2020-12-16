/* run.config
OPT: @MACHDEP@ @CXX@ -print
COMMENT: test handling of built-in nullptr_t
*/

#include <cstddef>

std::nullptr_t x = 0;

int main() {
  if (x == 0) return 0;
  return 1;
}
