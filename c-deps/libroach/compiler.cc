#include <cstdio>
#include <cassert>
#include <memory>

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"

#include "ast.h"
#include "parser.h"
#include "kaleidoscpe_jit.h"

using std::vector;
using std::sprintf;
using std::string;
using std::pair;
using std::unique_ptr;
using std::make_unique;

using llvm::Function;
using llvm::Value;
using llvm::LLVMContext;
using llvm::IRBuilder;
using llvm::Module;
using llvm::Type;
using llvm::PointerType;
using llvm::BasicBlock;

LLVMContext TheContext;
static IRBuilder<> Builder(TheContext);
std::unique_ptr<Module> TheModule;
std::unique_ptr<llvm::legacy::FunctionPassManager> TheFPM;

struct Variable {
  VarType type;
  llvm::Type* llvmType;
  llvm::AllocaInst* allocaInst;  // Space for the value.

  Variable(VarType type, llvm::Type* llvmType, llvm::AllocaInst* allocaInst)
    : type(type), llvmType(llvmType), allocaInst(allocaInst) {}
};

llvm::Type* getLLVMType(VarType type) {
  switch(type) {
  case type_double:
    return Type::getDoubleTy(TheContext);
  case type_byte:
    return Type::getInt8Ty(TheContext);
  case type_bool:
    return Type::getInt1Ty(TheContext);
  case type_byte_ptr:
    return PointerType::get(Type::getInt8Ty(TheContext), 0 /* address_space */);
  }
}

llvm::Value* getZeroVal(VarType type) {
  auto llvmType = getLLVMType(type);
  assert(llvmType);
  switch(type) {
  case type_double:
    // TODO(andrei): can I use getNullValue() here?
    return llvm::ConstantFP::get(TheContext, llvm::APFloat(0.0));
  case type_byte:
  case type_bool:
  case type_byte_ptr:
    return llvm::Constant::getNullValue(llvmType);
  }
}

// Variable name to space where the value is stored.
static std::map<string, Variable> NamedValues;

// Gets a copy.
unique_ptr<Variable> getVar(const string& name) {
  auto it = NamedValues.find(name);
  if (it == NamedValues.end()) {
    return nullptr;
  }
  return make_unique<Variable>(it->second);
}

std::unique_ptr<llvm::orc::KaleidoscopeJIT> TheJIT;
// Map of function name to the (latest) prototype declared with that name.
std::map<string, std::unique_ptr<PrototypeAST>> FunctionProtos;

CodegenRes ExprAST::codegen() {
  auto* val = codegenExpr();
  return CodegenRes(val != nullptr, false);
}

// resolveFunction takes a function name and returns the corresponding Function
// from the current module (if present) or generates the function from a
// registered prototype if the function had previously been generated in
// another module.
Function* resolveFunction(const string& name) {
  Function* f = TheModule->getFunction(name);
  if (f) {
    return f;
  }
  auto it = FunctionProtos.find(name);
  if (it != FunctionProtos.end()) {
    return it->second->codegen();
  }
  return nullptr;
}

// Create an alloca instruction in the entry block of the function. This is
// used for mutable variables etc.
static llvm::AllocaInst* createEntryBlockAlloca(
    Function* fun,
    const std::string& varName,
    llvm::Type* type) {
  IRBuilder<> TmpB(
      &fun->getEntryBlock(), fun->getEntryBlock().begin());
  return TmpB.CreateAlloca(type, 0, varName.c_str());
}

Value* NumberExprAST::codegenExpr() {
  if (isFP) {
    return llvm::ConstantFP::get(TheContext, llvm::APFloat(dval));
  } else if (isInt) {
    return llvm::Constant::getIntegerValue(Type::getInt8Ty(TheContext), 
        llvm::APInt(8, ival, false /* signed */));
  } else {
    llvm::Constant* constArr = llvm::ConstantDataArray::getString(
        TheContext, sval, true /* AddNull */);
    llvm::ArrayType* arrayTy = llvm::ArrayType::get(
        Type::getInt8Ty(TheContext), sval.length() + 1);
    llvm::GlobalVariable* gvarArrayStr = new llvm::GlobalVariable(
      *TheModule,
      arrayTy,
      /*isConstant=*/true,
      /*Linkage=*/llvm::GlobalValue::PrivateLinkage,
      /*Initializer=*/0, // has initializer, specified below
      /*Name=*/".str");
      gvarArrayStr->setAlignment(1);
    gvarArrayStr->setInitializer(constArr);
      
    
     std::vector<llvm::Constant*> idxs;
     llvm::ConstantInt* idx0 = llvm::ConstantInt::get(
         TheContext, llvm::APInt(32, 0));
     idxs.push_back(idx0);
     idxs.push_back(idx0);
     llvm::Constant* startPtr = llvm::ConstantExpr::getGetElementPtr(
         arrayTy,
         gvarArrayStr, idxs);
     return startPtr;
  }
}

Value* VariableExprAST::codegenExpr() {
  unique_ptr<Variable> v = getVar(name);
  if (!v) {
    char msg[1000];
    std::sprintf(msg, "unknown variable %s", name.c_str());
    return logErrorV(msg);
  }
  // Load the value from memory.
  return Builder.CreateLoad(v->allocaInst, name.c_str());
}

Value* UnaryExprAST::codegenExpr() {
  VariableExprAST* varAST = nullptr;
  unique_ptr<Variable> var;
  switch (op) {
  case '&':
    varAST = dynamic_cast<VariableExprAST*>(operand.get());
    if (!varAST) {
      return logErrorV("address of can only be applied to variables");
    }
    var = getVar(varAST->getName());
    if (!var) {
      char msg[1000];
      sprintf(msg, "unknown variable: %s", varAST->getName().c_str());
      return logErrorV(msg);
    }
    // The var itself is the address we're looking for.
    return var->allocaInst;
  case '*':
    varAST = dynamic_cast<VariableExprAST*>(operand.get());
    if (!varAST) {
      return logErrorV("dereferencing can only be applied to variables");
    }
    var = getVar(varAST->getName());
    if (!var) {
      char msg[1000];
      sprintf(msg, "unknown variable: %s", varAST->getName().c_str());
      return logErrorV(msg);
    }
    if (var->type != type_byte_ptr) {
      return logErrorV("can only dereference pointers");
    }
    {
      Value* loadPtr = Builder.CreateLoad(var->allocaInst, "load_ptr");
      return Builder.CreateLoad(loadPtr, "deref");
    }
  default:
    char msg[1000];
    sprintf(msg, "unknown unary op: %c", op);
    return logErrorV(msg);
  }
}

Value* BinaryExprAST::codegenExpr() {
  // The assignment operator is a special case because we don't want to emit
  // code for the LHS.
  if (op == '=') {
    // Check that the lhs is a variable reference.
    VariableExprAST* varAST = dynamic_cast<VariableExprAST*>(lhs.get());
    if (!varAST) {
      return logErrorV("destination of assignment must be a variable");
    }
    // Codegen the RHS.
    Value* r = rhs->codegenExpr();

    // Lookup the name.
    unique_ptr<Variable> var = getVar(varAST->getName());
    if (!var) {
      char msg[1000];
      sprintf(msg, "unknown variable: %s", varAST->getName().c_str());
      return logErrorV(msg);
    }
    Builder.CreateStore(r, var->allocaInst);
    // Return the result of the rhs.
    return r;
  }

  Value* l = lhs->codegenExpr();
  Value* r = rhs->codegenExpr();

  if (!l || !r) {
    return nullptr;
  }

  switch (op) {
  case '+':
    // return Builder.CreateFAdd(l, r, "addtmp");
    return Builder.CreateAdd(l, r, "addtmp");
  case '-':
    // return Builder.CreateFSub(l, r, "subtmp");
    return Builder.CreateSub(l, r, "subtmp");
  case '*':
    // return Builder.CreateFMul(l, r, "multmp");
    return Builder.CreateMul(l, r, "multmp");
  case '<':
    // compare unordered less than
    // !!! l = Builder.CreateFCmpULT(l, r, "cmptmp");
    l = Builder.CreateICmpULT(l, r, "cmptmp");
    // !!!
    // Convert bool 0/1 to double 0.0 or 1.0
    // return Builder.CreateUIToFP(
    //     l, Type::getDoubleTy(TheContext), "booltmp");
  default:
    char msg[1000];
    sprintf(msg, "invalid bin op: %c", op);
    return logErrorV(msg);
  }
}

Value* CallExprAST::codegenExpr() {
  // Resolve the function, either in the current module or in the list of
  // functions in all the modules.
  Function* calleeFun = resolveFunction(callee);
  if (!calleeFun) {
    char msg[1000];
    sprintf(msg, "unknown function referenced: %s", callee.c_str());
    return logErrorV(msg);
  }

  if (calleeFun->arg_size() != args.size()) {
    char msg[1000];
    sprintf(msg, "incorrect # arguments passed to %s: expected %lu, got %lu",
        callee.c_str(), calleeFun->arg_size(), args.size());
    return logErrorV(msg);
  }

  vector<Value*> argsV;
  for (const std::unique_ptr<ExprAST>& a : args) {
    Value* v = a->codegenExpr();
    if (!v) {
      return nullptr;
    }
    argsV.push_back(v);
  }
  return Builder.CreateCall(calleeFun, argsV, "calltmp");
}

Function* PrototypeAST::codegen() const {
  // The signature of the params.
  vector<Type*> paramTypes;
  for (size_t i = 0; i < argNames.size(); i++) {
    llvm::Type* llvmType = getLLVMType(argTypes[i]);
    if (llvmType == nullptr) return nullptr;
    paramTypes.push_back(llvmType); 
  }
  llvm::Type* retLLVMType = getLLVMType(retType);
  if (retLLVMType == nullptr) return nullptr;
  llvm::FunctionType* ft = llvm::FunctionType::get(
      retLLVMType, paramTypes, false /* isVarArg */);
  // Insert the function into the module.
  Function* f = Function::Create(ft, Function::ExternalLinkage, name, TheModule.get());

  // Set argument names;
  int idx = 0;
  for (auto& p : f->args()) {
    p.setName(argNames[idx++]);
  }
  return f;
}

Function* FunctionAST::codegen() {
  const PrototypeAST& p = *proto;
  // Transfer ownership of the prototype to the FunctionProtos map.
  FunctionProtos[p.getName()] = std::move(proto);
  Function* f = resolveFunction(p.getName());
  // We just added the function above.
  assert(f);

  BasicBlock *bb = BasicBlock::Create(TheContext, "entry", f);
  Builder.SetInsertPoint(bb);

  // Record the function arguments in the NamedValues map.
  NamedValues.clear();
  int i = 0;
  for (auto& arg : f->args()) {

    VarType type = p.getArgType(i);
    llvm::Type* llvmType = arg.getType();
    // Create an alloca for this variable.
    llvm::AllocaInst* alloca = createEntryBlockAlloca(f, arg.getName(), llvmType);
    // Store the initial value into the alloca.
    Builder.CreateStore(&arg, alloca);

    // Add the variable to the symbol table.
    NamedValues.insert(std::make_pair(arg.getName(), Variable(type, llvmType, alloca)));
    i++;
  }

  auto bodyRes = body->codegen();
  if (!bodyRes.success) {
    // In case of error in the body, we erase the function so it can be defined
    // again.
    f->eraseFromParent();
    return nullptr;
  }
  // bool xxx = (p.getName() != "magic");

  if (p.getName() != "magic") {
    BasicBlock* lastBlock = Builder.GetInsertBlock();
    if (lastBlock->empty()) {
      Builder.CreateRet(llvm::ConstantFP::get(TheContext, llvm::APFloat(0.0)));
    }
    // !!! now the return value is in the generated code, but I should assert that.
    // Builder.CreateRet(retVal);
  } else {
    // fprintf(stderr, "!!! FunctionAST::codegen 8\n");
    // Function* parentFun = Builder.GetInsertBlock()->getParent();
    // BasicBlock* b2 = BasicBlock::Create(TheContext, "b2", parentFun);
    // BasicBlock* b3 = BasicBlock::Create(TheContext, "b3", parentFun);
    //
    // Value* arg0 = NamedValues[f->args().begin()->getName()];
    // auto condCode = Builder.CreateFCmpONE(
    //     arg0, llvm::ConstantFP::get(TheContext, llvm::APFloat(0.0)), "ifcond");
    // Builder.CreateCondBr(condCode, b2, b3);
    //
    // Builder.SetInsertPoint(b2);
    // auto bogusRet = llvm::ConstantFP::get(TheContext, llvm::APFloat(1.0));
    // Builder.CreateRet(bogusRet);
    //
    // Builder.SetInsertPoint(b3);
    // bogusRet = llvm::ConstantFP::get(TheContext, llvm::APFloat(2.0));
    // Builder.CreateRet(bogusRet);
  }
  
  fprintf(stderr, "!!! Compiled to:\n");
  f->print(llvm::errs());

  // Validate the generated code, checking for consistency.
  assert(!llvm::verifyFunction(*f, &llvm::errs()));

  TheFPM->run(*f);

  return f;
}

CodegenRes IfStmtAST::codegen() {
  Value* condCode = condExpr->codegenExpr();
  if (!condCode) return CodegenRes(false, false); 
  // Convert condition to a bool by comparing non-equal to 0.
  condCode = Builder.CreateICmpNE(
      condCode,
      llvm::Constant::getNullValue(condCode->getType()), "ifcond");
      // !!! llvm::Constant::get(TheContext, llvm::APFloat(0)), "ifcond");

  // Get a reference to the function in which we're generating code. We'll
  // create new blocks in this function.
  Function* parentFun = Builder.GetInsertBlock()->getParent();

  // Create blocks for the then and else cases. 
  // The 'then' block is inserted at the end of the function; the others will
  // be inserted later.
  BasicBlock* thenBlock = BasicBlock::Create(TheContext, "then", parentFun);
  BasicBlock* elseBlock = BasicBlock::Create(TheContext, "if");
  BasicBlock* mergeBlock = BasicBlock::Create(TheContext, "ifcont");
  Builder.CreateCondBr(condCode, thenBlock, elseBlock);

  // Emit "then" code into a new block.
  Builder.SetInsertPoint(thenBlock);
  auto thenRes = thenStmt->codegen();
  if (!thenRes.success) return thenRes;
  if (!thenRes.ret) {  
    // Unconditional jump after the if/then/else block.
    Builder.CreateBr(mergeBlock);
  }

  // Emit "else" code into a new block.
  parentFun->getBasicBlockList().push_back(elseBlock);
  Builder.SetInsertPoint(elseBlock);
  auto elseRes = elseStmt->codegen();
  if (!elseRes.success) return elseRes;
  if (!elseRes.ret) {
    // Unconditional jump after the if/then/else block.
    Builder.CreateBr(mergeBlock);
  }
  
  // Emit the "merge" code.
  parentFun->getBasicBlockList().push_back(mergeBlock);
  Builder.SetInsertPoint(mergeBlock);
  return CodegenRes(true, false);
}

CodegenRes ReturnStmtAST::codegen() {
  Value* retVal = expr->codegenExpr();
  if (retVal == nullptr) return CodegenRes(false, false);
  Builder.CreateRet(retVal);
  return CodegenRes(true, true);
}

// Output for-loop as:
//   var = alloca double
//   ...
//   start = startexpr
//   store start -> var
//   goto loop
// loop:
//   <code for body>
//   step = stepexpr
//   endcond = endexpr
//   curvar = load var
//   nextvar = curvar + step
//   store nextvar -> var
//   br endcond, loop, afterloop
// afterloop:
CodegenRes ForStmtAST::codegen() {
  Function* fun = Builder.GetInsertBlock()->getParent();
  // TODO(andrei): this variable shouldn't always be a double.
  llvm::AllocaInst* alloca = createEntryBlockAlloca(
      fun, varName, Type::getDoubleTy(TheContext));

  // Emit the start code first, without the loop variable in scope.
  Value* startVal = start->codegenExpr();
  if (!startVal) return CodegenRes(false, false);

  Builder.CreateStore(startVal, alloca);

  // Make the new basic block for the loop header, inserting after current
  // block.
  Function* parentFun = Builder.GetInsertBlock()->getParent();
  BasicBlock* loopBB = BasicBlock::Create(TheContext, "loop", parentFun);
  // Insert an explicit fall through from the current block to the LoopBB.
  Builder.CreateBr(loopBB);

  // Start insertion in LoopBB.
  Builder.SetInsertPoint(loopBB);

  // Within the loop, the variable is defined equal to the variable we just
  // introduced. If it shadows an existing variable, we have to restore it, so
  // save it now.
  unique_ptr<Variable> oldLoopVar = getVar(varName);
  NamedValues.insert(std::make_pair(varName, Variable(type_double, getLLVMType(type_double), alloca)));
  // Generate code for the body. The generated Value is ignored.
  CodegenRes bodyRes = body->codegen();
  if (!bodyRes.success) return bodyRes;

  Value* endCond = nullptr;
  if (!bodyRes.ret) {
    // Emit the step value.
    Value* stepVal = step->codegenExpr();
    if (!stepVal) return CodegenRes(false, false);
    // Reload, increment, and restore the alloca. This handles the case where the
    // body of the loop mutates the variable.
    Value* curLoopVarVal = Builder.CreateLoad(alloca);
    Value* nextLoopVar = Builder.CreateFAdd(curLoopVarVal, stepVal, "nextvar");
    Builder.CreateStore(nextLoopVar, alloca);

    // Compute and evaluate the end condition.
    endCond = end->codegenExpr();
    if (!endCond) return CodegenRes(false, false);
    // Convert condition to a bool by comparing non-equal to 0.0.
    endCond = Builder.CreateFCmpONE(
      endCond, llvm::ConstantFP::get(TheContext, llvm::APFloat(0.0)), "loopcond");
  }
  
  // Create the "after loop" block and insert it.
  BasicBlock* afterLoopBB = BasicBlock::Create(TheContext, "afterloop", parentFun);
  // Insert the conditional branch into the end of afterLoopBB.
  if (endCond != nullptr) {
    Builder.CreateCondBr(endCond, loopBB, afterLoopBB);
  }
  
  // Any new code will be inserted in AfterBB.
  Builder.SetInsertPoint(afterLoopBB);

  // Restore the unshadowed variable.
  if (oldLoopVar != nullptr) {
    NamedValues.insert(std::make_pair(varName, *oldLoopVar));
  } else {
    NamedValues.erase(varName);
  }
  return CodegenRes(true, false);
}

CodegenRes BlockStmtAST::codegen() {
  for (const std::unique_ptr<StatementAST>& e : body) {
    auto stmtRes = e->codegen();
    if (!stmtRes.success) return stmtRes;
    if (stmtRes.ret) {
      return CodegenRes(true, true);
    }
  }
  return CodegenRes(true, false);
}

CodegenRes VariableDeclAST::codegen() {
  Function* fun = Builder.GetInsertBlock()->getParent();

  llvm::Type* llvmType = getLLVMType(type);
  if (llvmType == nullptr) return CodegenRes(false, false);

  // Emit the initializer before adding the variable to scope, this prevents
  // the initializer from referencing the variable itself, and permits stuff
  // like this:
  //  var a = 1
  //  {
  //    var a = a + 1  # refers to outer 'a'.
  //  }
  Value* initVal;
  if (val) {
    initVal = val->codegenExpr();
    if (initVal == nullptr) return CodegenRes(false, false);
  } else {
    initVal = getZeroVal(type);
  }
  // Allocate space for the variable on the heap. 
  llvm::AllocaInst *alloca = createEntryBlockAlloca(fun, name, llvmType);
  // Store the initial value in the allocated memory.
  Builder.CreateStore(initVal, alloca);
  
  // Remember this binding.
  // TODO(andrei): When do we remove the variable from scope?
  NamedValues.insert(std::make_pair(name, Variable(type, llvmType, alloca)));
  return CodegenRes(true, false);
}
