#include <cstdio>
#include <cstring>

#ifdef LLVM_ON_WIN32
#define DLLEXPORT __declspec(dllexport)
#else
#define DLLEXPORT
#endif

/// putchard - putchar that takes a double and returns 0.
extern "C" DLLEXPORT double putchard(double x) {
  fputc((char)x, stderr);
  return 0;
}

extern "C" DLLEXPORT char* skip_checksum(char *s) {
  return s+4;
}

extern "C" DLLEXPORT char* skip_bytes(char *s, char numBytes) {
  return s+numBytes;
}

extern "C" DLLEXPORT char* skip_byte(char *s) {
  return s+1;
}

extern "C" DLLEXPORT char* skip_int(char *s) {
  while (true) {
    if (*s & 128) {
      s++;
      continue;
    }
    break;
  }
  return ++s;
}

extern "C" DLLEXPORT char my_strcmp(const char *str1, char l1, const char *str2, char l2) {
  // return char(strcmp(str1, str2)); 
  char l = l1;
  if (l2 < l1) l = l2;
  for (int i = 0; i < l; i++) {
    if (str1[i] < str2[i]) {
      return -1;
    }
    if (str1[i] > str2[i]) {
      return 1;
    }
  }
  return 0;
}

extern "C" DLLEXPORT char streq(const char *str1, char l1, const char *str2, char l2) {
  if (my_strcmp(str1, l1, str2, l2) == 0) {
    return 1;
  }
  return 0;
}
