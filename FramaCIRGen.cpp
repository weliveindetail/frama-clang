/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-Clang                                      */
/*                                                                        */
/*  Copyright (C) 2012-2020                                               */
/*    CEA (Commissariat à l'énergie atomique et aux énergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file LICENSE).                      */
/*                                                                        */
/**************************************************************************/

//
// Description:
//   Definition of a translator clang -> intermediate_format (-> cabs -> cil).
//

#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Basic/FileManager.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/CompilerInvocation.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/Utils.h"
#include "clang/Sema/Sema.h"
#include "clang/Sema/Scope.h"
#include "clang/AST/Comment.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Basic/Version.h"

#include "llvm/Support/Path.h"
#include "llvm/Support/Host.h"
#include "llvm/ADT/ArrayRef.h"
#include <iostream>
#include <fstream>
#include <sstream>
#include <cstddef>
#include <list>
#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif

#include "ClangVisitor.h"

#ifndef CLANG_BIN_DIR
#define CLANG_BIN_DIR ""
#endif

bool FramacVisitor::HandleTopLevelDecl(clang::DeclGroupRef Decls) {
  if (_ghost) {
    addGhostDecl(Decls);
    clang::DeclGroupRef::iterator i = Decls.begin();
    clang::DeclGroupRef::iterator end = Decls.end();
    //bool res = true;
    while (i != end) {
      if (!TraverseDecl(*i)) break; //{ res = false; break; }
      i++;
    }
    return false; //traversal has already been done
  }
  else return true; // real declaration
}

/*! @class ProcessArguments
 *  @brief The class ProcessArguments defines the options of the translator
 *    from the command-line arguments.
 */
class ProcessArguments {
private:
  bool _isValid;
  // clang::CompilerInvocation* _invocation;
  std::string _output;
  std::vector<std::string> _includes;
  bool _doesStopAnnotError;
  bool _doesGenerateImplicitMethods;
  bool _isVerbose;
  bool _hasLanguageSpec;
  const char* _LanguageSpec;
  bool _doesGenerateBareFunctions;

public:
  ProcessArguments(/* clang::CompilerInvocation* invocation, */
      int argc, char** argv)
    : _isValid(true), /* _invocation(invocation), */ _doesStopAnnotError(false),
      _doesGenerateImplicitMethods(false), _isVerbose(false),
      _hasLanguageSpec(false), _LanguageSpec(NULL),
      _doesGenerateBareFunctions(false)
    { int uArg = argc-2;
      while (_isValid && (uArg >= 0))
        _isValid = process(argv + (argc - uArg - 1), uArg);
      // _isValid = _isValid
      //   && _invocation->getFrontendOpts().Inputs.size() > 0;
    }

  bool process(char** argument, int& currentArgument);
  void printUsage(std::ostream& osOut) const
    { std::cout << "Usage of FramaCIRGen :\n"
        << "FramaCIRGen [option]+ input-files -o framac-ir-outfile \n"
        << "  where option can be one of the following options:\n";
      std::cout << "    -Idirectory\tfor specifying an include directory\n";
      std::cout << "\nexample: FramaCIRGen -I. myfile.cpp -o myfile.fir\n";
      std::cout << std::endl;
    }
   bool isValid() const { return _isValid; }
   bool annotError() const { return _doesStopAnnotError; }
   bool doesGenerateImplicitMethods() const
     { return _doesGenerateImplicitMethods; }
   bool isVerbose() const { return _isVerbose; }
   bool hasLanguageSpec() const { return _hasLanguageSpec; }
   bool isCXXLanguage() const {
     return _LanguageSpec && strcmp(_LanguageSpec,"c++")==0;
   }
   bool doesGenerateBareFunctions() const { return _doesGenerateBareFunctions; }
   const std::string& getOutputFile() const { return _output; }
};

bool
ProcessArguments::process(char** argument, int& currentArgument) {
  //std::cout << "process argument " << *argument << std::endl;
  if (argument[0][0] == '-') {
    switch (argument[0][1]) {
// already handled by default clang::createInvocationFromCommandLine below
#if 0
      case 'I':
        if (argument[0][2] != '\0') {
          _includes.push_back(argument[0]+2);
          // _invocation->getPreprocessorOpts().Includes
          //   .push_back(argument[0]+2);
          _invocation->getHeaderSearchOpts().AddPath(argument[0]+2,
              clang::frontend::System, false, true);
          --currentArgument;
        }
        else {
          if (currentArgument == 0) {
            printUsage(std::cout);
            return false;
          };
          _includes.push_back(argument[1]);
          // _invocation->getPreprocessorOpts().Includes.push_back(argument[1]);
          _invocation->getHeaderSearchOpts().AddPath(
           argument[1],
           clang::frontend::System, false, true);
          currentArgument -= 2;
        };
        return true;
#endif
      case 'o':
        if (currentArgument == 0 || _output != "") {
          printUsage(std::cout);
          return false;
        };
        currentArgument -= 2;
        _output = argument[1];
        _isValid = true;
        return true;
      case 'v': 
        currentArgument--;
        _isVerbose=true;
        return true;
      case 'x':
        if (currentArgument == 0) {
          printUsage(std::cout);
          return false;
        } else {
          currentArgument--;
          _hasLanguageSpec=true;
          _LanguageSpec = argument[1];
          currentArgument -= 2;
          return true;
        }
      case 'b':
        if (currentArgument == 0) {
          printUsage(std::cout);
          return false;
        }
        else {
          currentArgument--;
          _doesGenerateBareFunctions=true;
        }
        return true;
      case '-':
        if (strcmp(argument[0],"--stop-annot-error")==0) {
          _doesStopAnnotError=true;
          --currentArgument;
        }
        else if (strcmp(argument[0],"--gen-impl-meth")==0) {
          _doesGenerateImplicitMethods=true;
          --currentArgument;
        }
        return true;
      default:
        --currentArgument;
        return true;
    };
  }
  else {
    // _invocation->getFrontendOpts().Inputs.push_back(
    //   clang::FrontendInputFile(argument[0], clang::IK_CXX));
    --currentArgument;
  };
  return true;
}

/*! The main function launches the clang parser with the options on the
 *    command-line. During the parsing, it collects the comments.
 *    Then it creates a FramaCIRGenAction for its visitor generating a full
 *    CIL AST thanks to the method clang::CompilerInstance::ExecuteAction.
 */
//#define DefinePreprocess
int
main(int argc, char** argv) {
  clang::CompilerInstance compiler;
#ifndef _WIN32
  compiler.createDiagnostics();
#else
  compiler.createDiagnostics(argc, argv);
#endif
  compiler.createFileManager();
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wcast-qual"

  ProcessArguments processArgument(argc, argv);
  if (argc == 1) {
    processArgument.printUsage(std::cout);
    return 0;
  };
  if (!processArgument.isValid()) {
    processArgument.printUsage(std::cout);
    return 0;
  };

  unsigned int clang_argc = 1;
  for (int i = 1; i<argc; i++) {
    if (strcmp("--stop-annot-error",argv[i]) != 0
        && strcmp("--gen-impl-meth",argv[i]) != 0) clang_argc++;
  }
  std::vector<const char*>
    my_argv(clang_argc+(processArgument.hasLanguageSpec()?1:3));
  llvm::MutableArrayRef<const char*>Argv(my_argv);
  /* When we are using system's headers, we have to rely on clang's own
     headers for some part of it. The issue is that clang is using a
     relative path for searching its headers, taking as base directory the
     path of the current binary (in argv[0]). There is apparently no way to
     override this computation except by recompiling clang with an appropriate
     option. Trying to install FramaCIRGen in the same directory is not
     practical (it won't be possible to run tests without having installed the
     plugin first, and if you use a system-wide clang and a user-installed
     Frama-C, this means requiring root privileges just for installing one
     binary). Instead, we play with that path directly here
   */
  llvm::SmallString<15> p(CLANG_BIN_DIR);
  llvm::sys::path::append(p,llvm::sys::path::filename(argv[0]));
  Argv[0] = p.c_str();
  for (int i = 1,j=1; i<argc; i++) {
    if (strcmp("--stop-annot-error", argv[i])!=0
        && strcmp("--gen-impl-meth", argv[i])!=0
        && strcmp("-b", argv[i])!=0) {
      Argv[j] = argv[i];
      j++;
    }
  }
#pragma GCC diagnostic pop
  Argv[clang_argc]="-Qunused-arguments";
  if (!processArgument.hasLanguageSpec()) {
    Argv[clang_argc+1] = "-x";
    Argv[clang_argc+2] = "c++";
  }
  llvm::IntrusiveRefCntPtr<clang::DiagnosticsEngine>
    Diag(&compiler.getDiagnostics());
  auto invocation = clang::createInvocationFromCommandLine(Argv,Diag);

  if (!invocation) {
    std::cerr << 
      "Could not create clang invocation; Aborting";
    exit(2);
  }

/*ProcessArguments processArgument(invocation, argc, argv);
  if (argc == 1) {
    processArgument.printUsage(std::cout);
    return 0;
  };
  if (!processArgument.isValid()) {
    processArgument.printUsage(std::cout);
    return 0;
  };
*/
  if (processArgument.hasLanguageSpec() && !processArgument.isCXXLanguage()) {
    std::cout
      << "Warning: you have explicitly set the language of the parsed file."
      << "Note that FramaCIRGen primary target is C++. All other languages "
      << "are not supported." << std::endl;
  } else {
    invocation->getLangOpts()->CPlusPlus = true;
    invocation->getLangOpts()->Bool = true;
    invocation->getLangOpts()->WChar = true;
    invocation->getLangOpts()->Exceptions = true;
    invocation->getLangOpts()->CXXExceptions = true;
    invocation->getLangOpts()->EmitAllDecls = true;
    invocation->getLangOpts()->GNUInline = true;
    invocation->getLangOpts()->Deprecated = true;
    invocation->getLangOpts()->WCharSize = 2;
    invocation->getLangOpts()->ImplicitInt = false;
  }
#ifdef DefinePreprocess
  invocation->getFrontendOpts().ProgramAction
    = clang::frontend::PrintPreprocessedInput;
#else
  invocation->getFrontendOpts().ProgramAction
    = clang::frontend::ParseSyntaxOnly; // passe du front-end ? RunAnalysis
#endif

#ifdef DefinePreprocess
   // llvm::Triple Triple(invocation->getTargetOpts().Triple);
   // std::cout << "os = " << Triple.getOS() << std::endl;
#else
  invocation->getPreprocessorOutputOpts().ShowComments = true;
#endif
#ifdef DefinePreprocess
  invocation->getPreprocessorOutputOpts().ShowMacros = true;
#endif
  std::shared_ptr<clang::CompilerInvocation>shared_invocation =
    std::make_shared<clang::CompilerInvocation>(*invocation);
  compiler.setInvocation(shared_invocation);
#ifdef DefinePreprocess
  clang::PrintPreprocessedAction prepro;
  compiler.ExecuteAction(prepro);
#else
  // clang::ASTDeclListAction declList;
  // compiler.ExecuteAction(declList);
  FramaCIRGenAction framaCIRGenAction(processArgument.getOutputFile(),
      compiler);
  if (processArgument.annotError()) framaCIRGenAction.setAnnotError();
  if (processArgument.doesGenerateImplicitMethods())
    framaCIRGenAction.setGenerateImplicitMethods();
  if (processArgument.doesGenerateBareFunctions())
    framaCIRGenAction.setGenerateBareFunctions();
  if (processArgument.isVerbose()) framaCIRGenAction.setVerbose();
  compiler.ExecuteAction(framaCIRGenAction);

  // We could also have used the function:
  // void ParseAST(Preprocessor &pp, ASTConsumer *C,
  //               ASTContext &Ctx, bool PrintStats = false,
  //               TranslationUnitKind TUKind = TU_Complete,
  //               CodeCompleteConsumer *CompletionConsumer = 0,
  //               bool SkipFunctionBodies = false);

#endif
  return 0;
}

