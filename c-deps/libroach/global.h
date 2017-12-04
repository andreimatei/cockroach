#ifndef GLOBAL_H 
#define GLOBAL_H

#include <memory>

#include "llvm/IR/Module.h"
#include "llvm/IR/LegacyPassManager.h"

#include "kaleidoscpe_jit.h"

class PrototypeAST;

extern std::unique_ptr<llvm::Module> TheModule;
extern llvm::LLVMContext TheContext;
extern std::unique_ptr<llvm::legacy::FunctionPassManager> TheFPM;
extern std::unique_ptr<llvm::orc::KaleidoscopeJIT> TheJIT;
extern std::map<std::string, std::unique_ptr<PrototypeAST>> FunctionProtos;

void ResetModule();

#endif
