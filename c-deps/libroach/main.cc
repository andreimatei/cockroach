#include <string>
#include <fstream>
#include <streambuf>

#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/IR/Verifier.h"

#include "parser.h"
#include "global.h"
#include "kaleidoscpe_jit.h"

using std::string;

void InitLLVM() {
  llvm::InitializeNativeTarget();
  llvm::InitializeNativeTargetAsmPrinter();
  llvm::InitializeNativeTargetAsmParser();

  TheJIT = std::make_unique<llvm::orc::KaleidoscopeJIT>();

  ResetModule();
}

void ResetModule() {
  // Open a new module.
  TheModule = std::make_unique<llvm::Module>("my cool jit", TheContext);
  TheModule->setDataLayout(TheJIT->getTargetMachine().createDataLayout());

  // Create a new pass manager attached to it.
  TheFPM = std::make_unique<llvm::legacy::FunctionPassManager>(TheModule.get());

  // Promote allocas to registers.
  TheFPM->add(llvm::createPromoteMemoryToRegisterPass());
  // Do simple "peephole" optimizations and bit-twiddling optzns.
  TheFPM->add(llvm::createInstructionCombiningPass());
  // Reassociate expressions.
  TheFPM->add(llvm::createReassociatePass());
  // Eliminate Common SubExpressions.
  TheFPM->add(llvm::createGVNPass());
  // Simplify the control flow graph (deleting unreachable blocks, etc).
  TheFPM->add(llvm::createCFGSimplificationPass());
  // !!!
  TheFPM->add(llvm::createVerifierPass(true /* fatalErrors */));

  TheFPM->doInitialization();
}

class StringReader {
private:
  string prog;
  size_t idx;
public:
  StringReader(const string& prog) : prog(prog), idx(0) {}
  ~StringReader() {}

  char GetNextChar() {
    if (idx < prog.length()) {
      return prog[idx++];
    }
    return EOF;
  }
};

StringReader* SR;

void CompileStr(const std::string& prog) {
  fprintf(stderr, "\n\n\nreceived program: %s\n\n\n", prog.c_str());
  // TODO(andrei): sr leaks
  SR = new StringReader(prog);
  //auto sr = new StringReader(prog);
  std::function<char()> nextCh = []() {
    return SR->GetNextChar();
  };
  GetNextChar = nextCh;
}

string FileToString(const string& path) {
  std::ifstream t(path);
  string str((std::istreambuf_iterator<char>(t)),
              std::istreambuf_iterator<char>());
  fprintf(stderr, "program: %s\n", str.c_str());
  return str;
}

std::string hex_to_string(const std::string& input)
{
    static const char* const lut = "0123456789ABCDEF";
    size_t len = input.length();
    if (len & 1) throw std::invalid_argument("odd length");

    std::string output;
    output.reserve(len / 2);
    for (size_t i = 0; i < len; i += 2)
    {
        char a = input[i];
        const char* p = std::lower_bound(lut, lut + 16, a);
        if (*p != a) throw std::invalid_argument("not a hex digit");

        char b = input[i + 1];
        const char* q = std::lower_bound(lut, lut + 16, b);
        if (*q != b) throw std::invalid_argument("not a hex digit");

        output.push_back(((p - lut) << 4) | (q - lut));
    }
    return output;
}

extern "C" char* skip_int(char *s);
extern "C" char* skip_checksum(char *s);
extern "C" char* skip_bytes(char *s, char numBytes);
extern "C" char* skip_byte(char *s);
extern "C" char streq(const char *str1, char l1, const char *str2, char l2);

void RunProgMain() {
  fprintf(stderr, "!!! RunProgMain\n");
  char* k1 = (char*)malloc(100);
  char* k2 = (char*)malloc(100);
  k1[0] = 0;
  k2[0] = 0;
  skip_int(k1);
  skip_byte(k1);
  skip_bytes(k1, 0);
  skip_checksum(k1);
  streq(k1, 0, k2, 0);
  llvm::JITSymbol exprSymbol = TheJIT->findSymbol("prog_main");
  assert(exprSymbol && "Function not found");

  // Get the symbol's address and cast it to the right type (takes no
  // arguments, returns a double) so we can call it as a native function.
  // !!! double (*fp)() = (double (*)())(intptr_t)(*exprSymbol.getAddress());
  // double res = fp();
  // fprintf(stderr, "Evaluated to: %f\n", res);
  char (*fp)(const char*,const char*) = (char(*)(const char*, const char*))(intptr_t)(*exprSymbol.getAddress());
  char* k = (char*)malloc(100);
  // char* v = (char*)malloc(100);

  string hexStr = "87200EEC0A130213ECF81213B47813021504348A06A41505348D204CD71503288904150328890216014E16014F13C095011384950113D29501161144454C4956455220494E20504552534F4E1605545255434B16176567756C617220636F757274732061626F766520746865";
  char res = fp(k, hex_to_string(hexStr).c_str());
  fprintf(stderr, "Evaluated to: %d\n", int(res));
}

// int main() {
//   GetNextChar = &getchar;
//
//   string progStr = FileToString("prog_real.in");
//   CompileStr(progStr);
//
//   InitParser();
//   InitLLVM();
//
//   MainLoop();
//
//   // Print out all of the generated code.
//   TheModule->print(llvm::errs(), nullptr);
//
//   RunProgMain();
//
//   return 0;
// }

