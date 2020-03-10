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
//   Implementation of the ACSL++ comment.
//

#include "AnnotationComment.h"
#include "ACSLComment.h"
#include "ACSLComponent.h"
#include "ACSLLexer.h"
#include "clang/Parse/Parser.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Sema/Scope.h"
#include <string>

bool
ACSLComment::checkAnnotation(const std::string& text, clang::SourceLocation clangLocation, const clang::Sema* sema, std::string& revised) {

  Acsl::Lexer lexer(sema);
  // We check the preprocessing directives by using builtin lexing (that is, not clang),
  // without macro expansion, in order to warn about preprocessing  directives that are not
  // supported by ACSL++
  lexer.setBuffer(text, clangLocation, 0, false, true);
  Acsl::Lexer::ReadResult r;
  do {
    r = lexer.readToken();
  } while (r != Acsl::Lexer::RRFinished);

  // Return best guess fixed-up text for further parsing
  // (string is empty if no best guess fixes were possible)
  revised = lexer._revised;
  if (lexer.hasErrors()) {
    // Print out the errors
    // FIXME - refactor to use Clang error diagnostic system
    // FIXME - errors are not counted
    std::list<Acsl::Lexer::Error>& errs = lexer.errorList();
    std::list<Acsl::Lexer::Error>::const_iterator iter = errs.begin();
    while (iter != errs.end()) {
       std::cerr << (*iter++).str() << std::endl;
    }
    return true;
  }
  return false;
}

ACSLComment::Kind
ACSLComment::getAnnotationKind(const std::string& text, clang::SourceLocation clangLocation, const clang::Sema* sema) {

  const char* start = text.c_str();
  size_t length = text.size();

  // arbitrary location since we are not using it to produce tokens or errors anyway
  Acsl::Lexer lexer(sema);
  // Only need the first token (or first few tokens)
  // So no clang, raw tokens -- So ACSL identifiers may not be macros
  lexer.setBuffer(text, clangLocation, 0, false, true);
  Acsl::Lexer::ReadResult res = lexer.readToken();
  if (res == Acsl::Lexer::RRFinished) {
    // empty annotation
    return KUndefined;
  }

  // FIXME - what if no tokens; what if not a content token

  const Acsl::DLexer::AbstractToken t = lexer.queryToken();
  if (t.getType() != Acsl::DLexer::AbstractToken::TKeyword) {
    return KUndefined;
  }

  Acsl::DLexer::KeywordToken key = (Acsl::DLexer::KeywordToken&)t;
  Acsl::DLexer::KeywordToken::Type ktype = (Acsl::DLexer::KeywordToken::Type)key.getType();

  std::string firstWord;
  auto iter = Acsl::DLexer::KeywordToken::_unprotectedKeywords.begin();
  while (iter != Acsl::DLexer::KeywordToken::_unprotectedKeywords.end()) {
    if ((*iter).second == ktype) { firstWord = iter->first; break; }
    iter++;
  }

  size_t endIndex = text.find(firstWord) + firstWord.size(); // Position in the buffer (locations are positions in file)


  // FIXME - are upper-case letters allowed in keywords?
  std::transform(firstWord.begin(), firstWord.end(), firstWord.begin(), ::tolower);
  if (firstWord == "ghost") {
    _startOfGhost = endIndex;
    return KGhost;
  }
  // Checks against all the keywords that can start a function or statement contract
  if (firstWord == "requires" || firstWord == "terminates"
      || firstWord == "decreases" || firstWord == "assigns"
      || firstWord == "ensures" || firstWord == "behavior"
      || firstWord == "assumes" || firstWord == "complete"
      || firstWord == "disjoint" || firstWord == "allocates"
      || firstWord == "frees" || firstWord == "exists")
    return KNext; /* function or statement */

  // FIXME Need to change this to ask the lexer for tokens
  if (firstWord == "for") {
    const char* lookForColon = &start[endIndex];
    size_t currentLength = length - endIndex;
    while (*lookForColon && *lookForColon != ':' && currentLength > 0) {
      ++lookForColon;
      --currentLength;
    };
    if (currentLength > 0 && *lookForColon == ':') {
      size_t firstIndex = endIndex + (lookForColon - &start[endIndex])+1;
      while (firstIndex < length && (isspace(start[firstIndex]) || start[firstIndex] == '@'))
        ++firstIndex;
      if (firstIndex >= length)
        return KNextStatement;
      if (!isalpha(start[firstIndex]))
        return KNextStatement;
      endIndex = firstIndex+1; 
      while (endIndex < length && isalpha(start[endIndex]))
        ++endIndex;
      firstWord = std::string(&start[firstIndex], (endIndex-firstIndex));
      std::transform(firstWord.begin(), firstWord.end(), firstWord.begin(),
          ::tolower);
    }
    else
      return KNextStatement;
  };
  if (firstWord == "loop" || firstWord == "for") {
    return KNextLoop; /* loop or statement */
  }
  if (firstWord == "assert")
    return KLabel; /* assertion */
  if (firstWord == "breaks" || firstWord == "continues"
      || firstWord == "returns")
    return KNextStatement; /* statement */
  if (firstWord == "invariant")
    return KOuterLoop;
  if (firstWord == "logic" || firstWord == "predicate" || firstWord == "global")
    return KGlobal;
  if (firstWord == "inductive" || firstWord == "axiomatic" 
      || firstWord == "lemma" || firstWord == "axiom")
    // strictly speaking, axiom cannot appear independently of an axiomatic,
    // but this error is caught in the GlobalAnnotation parser itself.
    return KGlobal;
  if (firstWord == "model")
    return KGlobal; /* declaration: variable or field */
  if (firstWord == "class" || firstWord == "type")
    return KGlobal; /* in the scope of the token */
  if (firstWord == "ghost")
    return KNext; /* KPrevious ??? declaration or statement */
  if (firstWord == "volatile")
    return KGlobal; /* declaration */
  return KUndefined;
}

void
ACSLComment::initFrom(const clang::Sema* sema) {
  if (_range.getBegin() == _range.getEnd())
    return;

  const clang::SourceManager& sourceMgr = sema->getPreprocessor().getSourceManager();

  clang::FileID beginFileId;
  clang::FileID endFileId;
  unsigned beginOffset;
  unsigned endOffset;

  std::tie(beginFileId, beginOffset)
      = sourceMgr.getDecomposedLoc(_range.getBegin());
  std::tie(endFileId, endOffset)
      = sourceMgr.getDecomposedLoc(_range.getEnd());

  const unsigned length = endOffset - beginOffset;
  if (length < 3) return;

  // The comment can't begin in one file and end in another.
  // FIXME - issue an error message for this ?
  if (beginFileId != endFileId) return;

  bool isInvalid = false;
  const char *bufferStart = sourceMgr.getBufferData(beginFileId, &isInvalid).data();
  if (isInvalid) return;

  // FIXME - The following looks at characters in the buffer directly and does not account for backslash-newlines or other character encodings
  _isLineComment = bufferStart[beginOffset+1] == '/'; // '*' for block comment
  _kind = KUndefined;
  if (bufferStart[beginOffset+2] != '@') return; // ACSL annotation must begin with @, without white space

  _commentText = new std::string( &bufferStart[beginOffset+3], _isLineComment ? length-3 : length-5);
  _commentTextLocation = _range.getBegin().getLocWithOffset(3);

  std::string revised;
  bool errors = checkAnnotation(*_commentText, _commentTextLocation, sema, revised);
    // Errors already printed
    if (!revised.empty()) {
    *_commentText = revised;
  } else if (errors) {
      delete _commentText;
    _commentText = NULL;
      return;
  }

  _kind = getAnnotationKind(*_commentText, _commentTextLocation, sema);
}


void
ACSLComment::parseGlobal(ForwardReferenceList& globals,
    ForwardReferenceList* classContent, const clang::DeclContext* clangContext,
    clang::ASTContext* astContext, clang::Sema* sema,
    clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable, location loc) {
  Acsl::GlobalAnnotation globalAnnotation(loc);
  Acsl::Parser parser(clangContext, astContext, sema, scope,
    clangUtils, globalAnnotation, rttiTable);
  parser.parse(getContent(),getSourceLocation());
  /*global_annotation*/list annots = globalAnnotation.getAnnot();
  while(annots) {
    global_annotation annot =
      (global_annotation)annots->element.container;
    if (classContent) {
      class_decl class_annot = class_decl_Class_annot(loc,annot);
      classContent->insertContainer(class_annot);
    }
    else {
      translation_unit_decl decl =
        translation_unit_decl_GlobalAnnotation(loc, annot);
      globals.insertContainer(decl);
    }
    annots = annots->next;
  }
}

void ACSLComment::parseGhostGlobal(
  //ForwardReferenceList& globals,
  //ForwardReferenceList* classContent,
    clang::DeclContext* clangContext,
    //    clang::ASTContext* astContext,
    clang::Sema* sema,
    clang::Scope* scope,
    clang::CompilerInstance& compilerInstance,
    clang::ASTConsumer* consumer) {
  llvm::StringRef code = llvm::StringRef(getContent());
  code = code.substr(_startOfGhost);
  clang::SourceLocation loc =
    getSourceLocation().getLocWithOffset(_startOfGhost);  // FIXME - check this for correct location
  clang::Preprocessor& cpp = compilerInstance.getPreprocessor();
  clang::Parser* parser =
    static_cast<clang::Parser*>(cpp.getCodeCompletionHandler());
  std::unique_ptr<llvm::MemoryBuffer> buff =
    llvm::MemoryBuffer::getMemBufferCopy(code, "ghost.cxx");
  clang::SourceManager& source_manager = compilerInstance.getSourceManager();
  clang::FileID file =
    source_manager.createFileID(
	    std::move(buff),clang::SrcMgr::C_User,0,0,loc);
  cpp.EnterSourceFile(file,0,loc);
  cpp.enableIncrementalProcessing();
  clang::Parser::DeclGroupPtrTy Decl;
  while (!parser->ParseTopLevelDecl(Decl)) {
    clang::DeclGroupRef DGR = Decl.get();
    consumer->HandleTopLevelDecl(DGR);
  }
  cpp.enableIncrementalProcessing(false);
  cpp.EndSourceFile();
}

void ACSLComment::parseGhostStatement(
    clang::DeclContext* clangContext,
     clang::Sema* sema,
    clang::Scope* scope,
    clang::CompilerInstance& compilerInstance,
    clang::ASTConsumer* consumer) {
  std::cerr << "Not yet implemented, ignoring ghost statement" << std::endl;
}

void
ACSLComment::parseCodeAnnotation(ForwardReferenceList& codeContainer,
    const clang::DeclContext* clangContext, clang::ASTContext* astContext,
    clang::Sema* sema, clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable, location loc) {
  Acsl::CodeAnnotation codeAnnotation(loc);
  Acsl::Parser parser(clangContext, astContext, sema, scope,
    clangUtils, codeAnnotation, rttiTable);
  parser.parse(getContent(), getSourceLocation());
  code_annotation annotation = codeAnnotation.extractAnnot();
  if (annotation)
    codeContainer.insertContainer(statement_Code_annot(
        codeAnnotation.extractLocation(), annotation));
}

/* code_annotation */ list
ACSLComment::parseLoopAnnotation(const clang::DeclContext* clangContext,
    clang::ASTContext* astContext, clang::Sema* sema, clang::Scope* scope,
    Clang_utils* clangUtils, const RTTITable& rttiTable, location loc) {
  Acsl::LoopAnnotation loopAnnotation(loc);
  Acsl::Parser parser(clangContext, astContext, sema, scope,
    clangUtils, loopAnnotation, rttiTable);
  parser.parse(getContent(),getSourceLocation());
  return loopAnnotation.extractResult();
}

void
ACSLComment::parseStatementAnnotation(ForwardReferenceList& codeContainer,
    const clang::DeclContext* clangContext, clang::ASTContext* astContext,
    clang::Sema* sema, clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable) {
  Acsl::StatementAnnotation statementAnnotation(codeContainer);
  Acsl::Parser parser(clangContext, astContext, sema, scope,
    clangUtils, statementAnnotation, rttiTable);
  parser.parse(getContent(),getSourceLocation());
}

void
ACSLComment::parseFunctionContract(option& /* function_contract */ contract,
    const clang::DeclContext* clangContext, clang::ASTContext* astContext,
    clang::Sema* sema, clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable) {
  Acsl::FunctionContract functionContract(nullptr);
  Acsl::Parser parser(clangContext, astContext, sema, scope,
    clangUtils, functionContract, rttiTable);
  parser.parse(getContent(),getSourceLocation());
  functionContract._loc = copy_loc(parser.lexer().seeTokenLocation());
  contract = opt_some_container(functionContract.getAnnot());
}

AnnotationComment*
AnnotationCommentFactory::createAnnotationComment(
      const clang::SourceManager& sourceMgr, const clang::SourceRange& range, const clang::Sema* sema)
{ ACSLComment* c = new ACSLComment(sourceMgr, range, sema);
  if (c->isValid()) return c;
  delete c;
  return NULL;
}

