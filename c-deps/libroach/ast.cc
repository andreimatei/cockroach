#include <string>
#include <sstream>

#include "ast.h"

std::string NumberExprAST::print() {
  std::ostringstream s;
  if (isFP) {
    s << dval;
  } else if (isInt) {
    s << ival;
  } else {
    s << sval;
  }
  return s.str();
}


std::string VariableExprAST::print() {
  return name;
}

std::string VariableDeclAST::print() {
  std::ostringstream s;
  s << "var " <<  name;
  if (val != nullptr) {
    s << " = " << val->print();
  }
  s << ";";
  return s.str();
}

std::string BinaryExprAST::print() {
  return "(" + lhs->print() + op + rhs->print() + ")";
}

std::string UnaryExprAST::print() {
  return op + operand->print();
}

std::string CallExprAST::print() {
  return callee + "(...)";
}

std::string IfStmtAST::print() {
  std::ostringstream s;
  s << "if (" <<  condExpr->print() << ") then (" << thenStmt->print() 
   << ") else (" << elseStmt->print() << ")";
  return s.str();
}

std::string ForStmtAST::print() {
  std::ostringstream s;
  s << "for " << varName  << " = (" << start->print() << "), " 
    << varName << " < (" << end->print() << "), (" << step->print() << ") "
    << body->print();
  return s.str();
}

std::string BlockStmtAST::print() {
  std::ostringstream s;
  s << "{\n";
  for (const std::unique_ptr<StatementAST>& e : body) {
    s << e->print() << "\n";
  }
  s << "}\n";
  return s.str();
}

std::string ReturnStmtAST::print() {
  std::ostringstream s;
  s << "return " << expr->print();
  return s.str();
}
