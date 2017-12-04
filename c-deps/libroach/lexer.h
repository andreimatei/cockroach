#ifndef LEXER_H
#define LEXER_H

#include <functional>
#include <string>

// The lexer returns tokens [0-255] if it is an unknown character, otherwise one
// of these for known things.
enum Token {
  tok_eof = -1,

  // commands
  tok_def = -2,
  tok_extern = -3,

  // primary
  tok_identifier = -4,
  tok_int_literal = -5,
  tok_fp_literal = -16,
  tok_str_literal = -17,
  tok_block_open = -11,
  tok_block_close = -12,
  tok_semi = -13,

  // control
  tok_if = -6,
  tok_then = -7,
  tok_else = -8,
  tok_for = -9, 
  tok_in = -10,
  tok_return = -14,

  // variable definition
  tok_var = -15
};


/// gettok - Return the next token from standard input.
int gettok(std::function<char()>);

extern std::string IdentifierStr; // Filled in if tok_identifier
extern long int IntVal;           // Filled in if tok_int_literal
extern double FPVal;              // Filled in if tok_fp_literal
extern std::string StrVal;        // Filled in if tok_str_literal

#endif
