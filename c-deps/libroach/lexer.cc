#include <string>

#include "lexer.h"

using std::string;

std::string IdentifierStr; // Filled in if tok_identifier
long int IntVal;           // Filled in if tok_int_literal
double FPVal;              // Filled in if tok_fp_literal
std::string StrVal;        // Filled in if tok_str_literal


const std::string hexDigits("0123456789ABCDEF");

char hexDigitToNum(char ch) {
  int value = hexDigits.find(ch);
  return char(value);
}

string ConvertHexString(string s) {
  if (s.length() < 2) return s;
  if (s[0] == '\\' && s[1] == 'x') {
    if (s.length() % 2 != 0) {
      fprintf(stderr, "invalid hex string\n");
      return "";
    }
    string res = "";
    for (size_t i = 2; i < s.length();) {
      char hi = s[i];
      char lo = s[i+1];
      char c = ((hexDigitToNum(hi) << 4) + hexDigitToNum(lo));
      res += c;
      i += 2;
    }
    return res;
  }
  return s;
}

/// gettok - Return the next token from standard input.
int gettok(std::function<char()> getch) {
  // static because a previous call may leave a character not consumed.
  static int lastCh = ' ';

  // Skip white space.
  while (isspace(lastCh)) {
    lastCh = getch();
  }

  if (isalpha(lastCh) || (lastCh == '_')) {  // identifier: [a-zA-Z][a-zA-Z0-9]_*
    IdentifierStr = lastCh;

    while (isalnum(lastCh = getch()) || (lastCh == '_')) {
      IdentifierStr += lastCh;
    }
    if (IdentifierStr == "def") {
      return tok_def;
    }
    if (IdentifierStr == "extern") {
      return tok_extern;
    }
    if (IdentifierStr == "if")
      return tok_if;
    if (IdentifierStr == "then")
      return tok_then;
    if (IdentifierStr == "else")
      return tok_else;
    if (IdentifierStr == "for")
      return tok_for;
    if (IdentifierStr == "return")
      return tok_return;
    if (IdentifierStr == "var")
      return tok_var;
    // !!! did I get rid of "in"?
    if (IdentifierStr == "in")
      return tok_in;
    return tok_identifier;
  }

  if (lastCh == '{') {
    lastCh = getch();
    return tok_block_open;
  }
  if (lastCh == '}') {
    lastCh = getch();
    return tok_block_close;
  }
  if (lastCh == ';') {
    lastCh = getch();
    return tok_semi;
  }

  bool found_dec = false;
  if (isdigit(lastCh) || lastCh == '.') { // Number: [0-9.]+
    std::string num;
    do {
      num += lastCh;
      lastCh = getch();
      if (lastCh == '.') {
        found_dec = true;
      }
    } while (isdigit(lastCh) || lastCh == '.');
    if (found_dec) {
      FPVal = strtod(num.c_str(), nullptr /* endptr */);
      return tok_fp_literal;
    } else {
      IntVal = strtol(num.c_str(), nullptr /* endptr */, 10 /* base */);
      return tok_int_literal;
    }
  }

  // parse a string literal
  if (lastCh == '"') {
    lastCh = getch();
    std::string lit;
    while (lastCh != '"') {
      lit += lastCh;
      lastCh = getch();
    }
    lastCh = getch(); // eat the closing "
    StrVal = ConvertHexString(lit);
    return tok_str_literal;
  }
  
  if (lastCh == '#') {
    // Comment until end of line.
    do {
      lastCh = getch();
    } while (lastCh != EOF && lastCh != '\n' && lastCh != '\r');
    if (lastCh != EOF) {
      return gettok(getch);
    }
  }
  
  // Check for end of file. Don't eat the EOF.
  if (lastCh == EOF) {
    return tok_eof;
  }

  // Otherwise, just return the character as its ascii value.
  int thisCh = lastCh;
  lastCh = getch();
  return thisCh;
}

