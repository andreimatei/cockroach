#ifndef PARSER_H
#define PARSER_H

#include "llvm/IR/Value.h"

void InitParser();
void MainLoop();
llvm::Value* logErrorV(const char* str);

extern std::function<char()> GetNextChar;

enum VarType {
  type_double = 0,
  type_byte = 1,
  type_byte_ptr = 2,
  type_bool = 3,
};

#endif
