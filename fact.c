#include <emscripten.h>

EMSCRIPTEN_KEEPALIVE
int fact(int n) {
  int res = 1;
  for (int i = 2; i <=n; i++) {
    res *= i;
  }
  return res;
}
