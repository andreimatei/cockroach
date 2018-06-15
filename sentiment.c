#include <emscripten.h>
#include <string.h>

int my_strstr(char* s1, char* s2) {
  for (;*s1; s1++) {
    char* h = s1;
    char* n = s2;
    for (;*h && *n && (*h == *n); h++, n++) {}
    if (!*n) {
      return 1;
    }
  }
  return 0;
}

int sentiment_nlp(char* s) {
  return my_strstr(s, "love");
}

int sentiment_emoji(char* s) {
  return my_strstr(s, ":)");
}

EMSCRIPTEN_KEEPALIVE
int test(char* s, int a, int b, int c) {
  return sentiment_nlp(s) || sentiment_emoji(s);
}

