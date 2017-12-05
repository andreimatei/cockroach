#include <cassert>
#include <memory>
#include <string>
#include <map>
#include <set>

#include "llvm/Support/raw_ostream.h"

#include "lexer.h"
#include "ast.h"
#include "global.h"

using std::string;
using std::unique_ptr;
using std::vector;
using std::move;

using llvm::Value;

std::set<char> UnaryOps;
std::function<char()> GetNextChar;

// CurTok/getNextToken - Provide a simple token buffer. CurTok is the current
// token the parser is looking at. getNextToken reads another token from the /
// lexer and updates CurTok with its results.
int CurTok;
int getNextToken() {
  CurTok = gettok(GetNextChar);
  return CurTok;
}

/// logError* - These are little helper functions for error handling.
unique_ptr<ExprAST> logError(const char* str) {
  fprintf(stderr, "logError: %s\n", str);
  return nullptr;
}

unique_ptr<PrototypeAST> logErrorP(const char* str) {
  logError(str);
  return nullptr;
}

Value* logErrorV(const char* str) {
  logError(str);
  return nullptr;
}

/// numberexpr ::= number
static std::unique_ptr<ExprAST> ParseNumberExpr(bool fp) {
  auto res = std::make_unique<NumberExprAST>(); 
  if (fp) {
   *res = NumberExprAST::FromFP(FPVal);
  } else {
   *res = NumberExprAST::FromInt(IntVal);
  }
  getNextToken(); // eat the literal
  return std::move(res);
}

static std::unique_ptr<ExprAST> ParseStringLiteral() {
  auto res = std::make_unique<NumberExprAST>(); 
  *res = NumberExprAST::FromStr(StrVal);
  getNextToken(); // eat the literal
  return std::move(res);
}

static std::unique_ptr<ExprAST> ParseExpression();
static std::unique_ptr<StatementAST> ParseStmt();

/// parenexpr ::= '(' expression ')'
static std::unique_ptr<ExprAST> ParseParenExpr() {
  getNextToken(); // eat '('
  auto ret = ParseExpression();
  if (!ret) {
    return nullptr;
  }
  if (CurTok != ')') {
    return logError("missing )");
  }
  getNextToken(); // eat ')'
  return ret;
}

/// identifierexpr
///   ::= identifier
///   ::= identifier '(' expression* ')'
static std::unique_ptr<ExprAST> ParseIdentifierExpr() {
  string id = IdentifierStr;
  getNextToken();  // eat the identifier name

  // Is this a variable reference?
  if (CurTok != '(') {
    return std::make_unique<VariableExprAST>(id);
  }

  // Continue paring a function call.
  getNextToken();  // eat '('
  vector<unique_ptr<ExprAST>> args;
  auto first = true;
  while (true) {
    if (CurTok == ')') {
      getNextToken();  // eat ')'
      break;
    }
    if (!first && CurTok != ',') {
      return logError("Expected ')' or ',' in argument list");
    }
    if (!first) {
      getNextToken();  // eat ','
    }
    first = false;
    auto arg = ParseExpression();
    if (arg == nullptr) {
      return nullptr;
    }
    args.push_back(move(arg));
  }
  return std::make_unique<CallExprAST>(id, std::move(args));
}

// ifstmt ::= 'if' expression 'then' stmt 'else' stmt
static std::unique_ptr<StatementAST> ParseIfStmt() {
  getNextToken(); // eat the if

  // parse the condition
  unique_ptr<ExprAST> cond = ParseExpression();
  if (!cond) {
    return nullptr;
  }
  
  // parse the then stmt
  if (CurTok != tok_then) {
    return logError("expected then");
  }
  getNextToken();  // eat the then
  unique_ptr<StatementAST> then = ParseStmt();
  if (!then) {
    return nullptr;
  }

  // parse the else stmt
  if (CurTok != tok_else) {
    return logError("expected else");
  }
  getNextToken();  // eat the else 
  unique_ptr<StatementAST> elseStmt = ParseStmt();
  if (!then) {
    return nullptr;
  }
  auto up = std::make_unique<IfStmtAST>(
      std::move(cond), std::move(then), std::move(elseStmt));
  return up;
}

/// forstmt ::= 'for' identifier '=' expr ',' expr (',' expr)? stmt
static unique_ptr<StatementAST> ParseForStmt() {
  getNextToken();  // eat the "for"

  if (CurTok != tok_identifier) {
    return logError("expected identifier after for");
  }

  std::string varName = IdentifierStr;
  getNextToken();  // eat identifier.

  if (CurTok != '=') {
    return logError("expected '=' after for");
  }
  getNextToken();  // eat '='.


  unique_ptr<ExprAST> start = ParseExpression();
  if (!start) {
    return nullptr;
  }
  if (CurTok != ',') {
    return logError("expected ',' after for start value");
  }
  getNextToken();

  unique_ptr<ExprAST> end = ParseExpression();
  if (!end) {
    return nullptr;
  }

  // The step value is optional.
  std::unique_ptr<ExprAST> step;
  if (CurTok == ',') {
    getNextToken();
    step = ParseExpression();
    if (!step) return nullptr;
  } else {
    // If a step is not specified, the default is 1.0.
    step = std::make_unique<NumberExprAST>(NumberExprAST::FromFP(1.0));
  }

  unique_ptr<StatementAST> body = ParseStmt();
  if (!body) return nullptr; 

  return std::make_unique<ForStmtAST>(
      varName, std::move(start), std::move(end), std::move(step), std::move(body));
}

/// returnStmt ::= 'return' expr
static unique_ptr<StatementAST> ParseReturnStmt() {
  getNextToken();  // eat the "return"
  std::unique_ptr<ExprAST> expr;
  expr = ParseExpression();
  if (!expr) return nullptr;
  return std::make_unique<ReturnStmtAST>(std::move(expr));
}

/// blockStmt ::= '{' (expr ';')* '}'
static unique_ptr<StatementAST> ParseBlockStmt() {
  getNextToken();  // eat '{'.
  std::vector<unique_ptr<StatementAST>> stmts;
  while (true) {
    if (CurTok == tok_semi) {
      getNextToken();  // eat ';'.
    }
    if (CurTok == tok_block_close ) {
      getNextToken();  // eat '}'.
      break;
    }
    std::unique_ptr<StatementAST> stmt;
    stmt = ParseStmt();
    if (!stmt) return nullptr;
    stmts.push_back(std::move(stmt));
  }
  return std::make_unique<BlockStmtAST>(std::move(stmts));
}

static std::unique_ptr<VarType> ParseDataType() {
  if (CurTok != tok_identifier) {
    fprintf(stderr, "expected type but found token: %d\n", CurTok);
    return nullptr;
  }
  if (IdentifierStr == "double") {
    return std::make_unique<VarType>(type_double);
  }
  if (IdentifierStr == "byte") {
    return std::make_unique<VarType>(type_byte);
  }
  if (IdentifierStr == "byte_ptr") {
    return std::make_unique<VarType>(type_byte_ptr);
  }
  fprintf(stderr, "didn't recognize type: %s\n", IdentifierStr.c_str());
  return nullptr;
}

/// ::= 'var' <identifier> <type> ('=' expression)?
static std::unique_ptr<StatementAST> ParseVariableDeclStmt() {
  getNextToken();  // eat the var.
  string name;
  // Initial value. Stays null if not specified.
  unique_ptr<ExprAST> val;
  
  if (CurTok != tok_identifier) {
    return logError("expected identifier after var");
  }
  name = IdentifierStr;

  getNextToken();  // eat the identifier.

  unique_ptr<VarType> type = ParseDataType();
  if (type == nullptr) {
    return logError("failed to parse type");
  }
  getNextToken();  // eat the data type.

  if (CurTok == '=') {
    getNextToken();  // eat the '='.
    val = ParseExpression();
    if (!val) {
      return nullptr;
    }
  }

  return std::make_unique<VariableDeclAST>(name, *type, std::move(val));
}

/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
///   ::= ifthenelse
//    ::= forexpr
//    ::= blockexpr
//    ::= VariableDeclExpr
//    ::= returnexpr
static std::unique_ptr<ExprAST> ParsePrimary() {
  switch (CurTok) {
  case tok_identifier:
    return ParseIdentifierExpr();
  case tok_fp_literal:
    return ParseNumberExpr(true /* fp */);
  case tok_int_literal:
    return ParseNumberExpr(false /* fp */);
  case tok_str_literal:
    return ParseStringLiteral();
  case '(':
    return ParseParenExpr();
  }
  if (isascii(CurTok)) {
    if (UnaryOps.find(CurTok) != UnaryOps.end()) {
      char op = CurTok;
      getNextToken();  // eat the unary operator
      auto operand = ParsePrimary();
      if (!operand) return nullptr;
      return std::make_unique<UnaryExprAST>(op, std::move(operand));
    }
  }

  fprintf(stderr, "unknown token when expecting an expression: %d\n", CurTok);
  return logError("unknown token when expecting an expression");
}

static std::unique_ptr<StatementAST> ParseStmt() {
  switch (CurTok) {
  default:
    fprintf(stderr, "unknown token when expecting an expression: %d\n", CurTok);
    return logError("unknown token when expecting an expression");
  case tok_identifier:
    return ParseExpression();
  case tok_fp_literal:
    return ParseExpression();
  case tok_int_literal:
    return ParseExpression();
  case '(':
    return ParseExpression();
  case tok_if:
    return ParseIfStmt();
  case tok_for:
    return ParseForStmt();
  case tok_block_open:
    return ParseBlockStmt();
  case tok_var:
    return ParseVariableDeclStmt();
  case tok_return:
    return ParseReturnStmt();
  }
}

std::map<char, int> BinopPrecedence;

int GetTokPrecedence() {
  if (!isascii(CurTok)) {
    // We use a really low precedence so that the token is always rejected by
    // operator-precedence parsing.
    return -1;
  }

    // Make sure it's a declared binop.
  int tokPrec = BinopPrecedence[CurTok];
  if (tokPrec <= 0) return -1;
  return tokPrec;
}

void InitParser() {
  UnaryOps.insert('&');
  UnaryOps.insert('*');

  // Install standard binary operators.
  // 1 is lowest precedence.
  BinopPrecedence['='] = 2;
  BinopPrecedence['!'] = 10;
  BinopPrecedence['<'] = 10;
  BinopPrecedence['+'] = 20;
  BinopPrecedence['-'] = 20;
  BinopPrecedence['*'] = 40;  // highest.

  // Prime the first token.
  //fprintf(stderr, "ready> ");
  getNextToken();
}

static unique_ptr<ExprAST> ParseBinOpRHS(
  int exprPrec,
  unique_ptr<ExprAST> lhs
);

/// expression
///   ::= primary binoprhs
static unique_ptr<ExprAST> ParseExpression() {
  auto lhs = ParsePrimary();
  if (!lhs) return nullptr;
  return ParseBinOpRHS(0 /* exprPrec */, std::move(lhs));
}

/// binoprhs
///   ::= ('+' primary)*
static std::unique_ptr<ExprAST> ParseBinOpRHS(
  int exprPrec,
  unique_ptr<ExprAST> lhs
) {
  // Keep consuming binops until we find one whose precedence is too low.
  // lhs keeps growing as lower and lower priority operators are encountered.
  while (1) {
    int tokPrec = GetTokPrecedence();
    if (tokPrec < exprPrec) {
      return lhs;
    }
    // We know that we're positioned on a binop, otherwise the precedence check
    // would have rejected the token.
    int binOp = CurTok;
    getNextToken();  // eat binop

    // Parse the primary expression after the binary operator.
    auto rhs = ParsePrimary();
    if (!rhs) {
      return nullptr;
    }

    // If binOp binds less tightly with RHS than the operator after RHS, let
    // the pending operator take RHS as its LHS.
    int nextPrec = GetTokPrecedence();
    if (tokPrec < nextPrec) {
      rhs = ParseBinOpRHS(tokPrec+1, std::move(rhs));
      if (!rhs) {
        return nullptr;
      }
    }

    // Merge lhs/rhs and continue parsing.
    lhs = std::make_unique<BinaryExprAST>(binOp, std::move(lhs), std::move(rhs));
  }
}

/// prototype
///   ::= <type> id '(' id type* ')'
static std::unique_ptr<PrototypeAST> ParsePrototype() {
  if (CurTok != tok_identifier) {
    return logErrorP("Expected type in prototype");
  }

  unique_ptr<VarType> type = ParseDataType();
  if (type == nullptr) return nullptr; 
  getNextToken();  // eat the return type

  if (CurTok != tok_identifier) {
    return logErrorP("Expected function name in prototype");
  }

  std::string fnName = IdentifierStr;
  getNextToken();  // eat the function name

  if (CurTok != '(') {
    return logErrorP("Expected '(' in prototype");
  }

  // Read the list of argument names.
  std::vector<std::string> argNames;
  std::vector<VarType> argTypes;
  while (true) {
    int tok = getNextToken();
    if (tok != tok_identifier) {
      break;
    }

    unique_ptr<VarType> type = ParseDataType();
    if (type == nullptr) return nullptr;
    argTypes.push_back(*type);

    tok = getNextToken();
    if (tok != tok_identifier) {
      return logErrorP("expected arg name");
    }

    argNames.push_back(IdentifierStr);

    tok = getNextToken();
    if (tok != ',') {
      break;
    }
  }

  if (CurTok != ')') {
    return logErrorP("Expected ')' in prototype");
  }

  getNextToken();  // eat ')'.

  return std::make_unique<PrototypeAST>(
      fnName, *type, std::move(argNames), std::move(argTypes));
}

/// definition ::= 'def' prototype expression
static std::unique_ptr<FunctionAST> ParseDefinition() {
  getNextToken();  // eat def.
  auto proto = ParsePrototype();
  if (!proto) {
    return nullptr;
  }
  if (auto e = ParseStmt()) {
    return std::make_unique<FunctionAST>(std::move(proto), std::move(e));
  }
  return nullptr;
}

/// external ::= 'extern' prototype
static std::unique_ptr<PrototypeAST> ParseExtern() {
  getNextToken();  // eat extern.
  return ParsePrototype();
}

/// toplevelexpr ::= expression
static std::unique_ptr<FunctionAST> ParseTopLevelExpr() {
  if (auto e = ParseExpression()) {
    // Make an anonymous prototype.
    auto proto = std::make_unique<PrototypeAST>(
        "__anon_expr", type_byte, 
        std::vector<std::string>(), std::vector<VarType>());
    // Generate a return statement.
    auto ret = std::make_unique<ReturnStmtAST>(std::move(e));
    return std::make_unique<FunctionAST>(std::move(proto), std::move(ret));
  }
  return nullptr;
}

//===----------------------------------------------------------------------===//
// Top-Level parsing
//===----------------------------------------------------------------------===//

static void HandleDefinition() {
  if (auto fnAST = ParseDefinition()) {
    if (auto* fnIR = fnAST->codegen()) {
      fprintf(stderr, "\n\n\nGenerated function:\n\n\n");
      fnIR->print(llvm::errs());
      fprintf(stderr, "\n");
      // Add a module with this function and create a new module for future
      // code.
      TheJIT->addModule(std::move(TheModule));
      ResetModule();
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

static void HandleExtern() {
  if (auto protoAST = ParseExtern()) {
    if (auto* fnIR = protoAST->codegen()) {
      //fprintf(stderr, "Read extern:");
      //fnIR->print(llvm::errs());
      //fprintf(stderr, "\n");
      // Add the signature to the list of functions.
      FunctionProtos[protoAST->getName()] = std::move(protoAST);
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

static void HandleTopLevelExpression() {
  // Evaluate a top-level expression into an anonymous function.
  if (auto fnAST = ParseTopLevelExpr()) {
    if (auto* fnIR = fnAST->codegen()) {
      fprintf(stderr, "Read a top-level expr:");
      fnIR->print(llvm::errs());

      // JIT the module containing the anonymous expression, keeping a handle
      // so we can free it later.
      llvm::orc::KaleidoscopeJIT::ModuleHandleT modHandle = TheJIT->addModule(
          std::move(TheModule));
      // Prepare for creating a future module.
      ResetModule();

      llvm::JITSymbol exprSymbol = TheJIT->findSymbol("__anon_expr");
      assert(exprSymbol && "Function not found");

      // Get the symbol's address and cast it to the right type (takes no
      // arguments, returns a double) so we can call it as a native function.
      // !!! double (*fp)() = (double (*)())(intptr_t)(*exprSymbol.getAddress());
      // double res = fp();
      // fprintf(stderr, "Evaluated to: %f\n", res);
      char (*fp)() = (char(*)())(intptr_t)(*exprSymbol.getAddress());
      char res = fp();
      fprintf(stderr, "Evaluated to: %d\n", int(res));

      // Remove the module with the anonymous function.
      TheJIT->removeModule(modHandle);
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

/// top ::= definition | external | expression | ';'
void MainLoop() {
  while (1) {
    //fprintf(stderr, "ready> ");
    switch (CurTok) {
    case tok_eof:
      return;
    case tok_semi: // ignore top-level semicolons.
      getNextToken();
      break;
    case tok_def:
      HandleDefinition();
      break;
    case tok_extern:
      HandleExtern();
      break;
    default:
      HandleTopLevelExpression();
      break;
    }
  }
}
