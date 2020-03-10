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
//   Definition of the ACSL++ comment.
//

#ifndef ACSL_CommentH
#define ACSL_CommentH

#include "clang/Frontend/CompilerInstance.h"
#include "AnnotationComment.h"

/*! @class ACSLComment
 *  @brief An ACSLComment object is stored each time the preprocessor
 *    encounters a comment that is valid (see the method isValid) as an ACSL++
 *    comment. This comment is then visited by the FramaCIRGenAction::Visitor
 *    and it is parsed at that time to produce valid annotations in the CIL AST.
 *
 *  @sa{ clang::Preprocessor::addCommentHandler,
 *       FramaCIRGenAction::ACSLCommentHandler, FramaCIRGenAction::Visitor,
 *       Acsl::Parser, Acsl::Parser::Parser, Acsl::Parser::parse
 *     }
 */

class ACSLComment : public AnnotationComment {
private:
 private:
  mutable size_t _startOfGhost;
  /// for ghost comments, offset where the code starts (i.e. after
  /// 'ghost' keyword itself).
public:
 ACSLComment(const clang::SourceRange& range) :
  AnnotationComment(range), _startOfGhost(0) {}
  ACSLComment(const clang::SourceManager& sourceMgr, clang::SourceRange range, const clang::Sema* sema)
    : AnnotationComment(range), _startOfGhost(0) { initFrom(sema); }
  ACSLComment(const ACSLComment& source)
    : AnnotationComment(source), _startOfGhost(source._startOfGhost) {}

  /*! checks annotation for improper use of preprocessor directives, returns true if errors found */
  virtual bool checkAnnotation(const std::string& text, clang::SourceLocation clangLocation, const clang::Sema* sema, std::string& revised) ;

  virtual Kind getAnnotationKind(const std::string& text, clang::SourceLocation clangLocation, const clang::Sema* sema) ;

  virtual void parseGlobal(ForwardReferenceList& globals,
    ForwardReferenceList* classContent, const clang::DeclContext* clangContext,
    clang::ASTContext* astContext, clang::Sema* sema,
    clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable, location loc);

  virtual void parseGhostGlobal(
    //    ForwardReferenceList& globals,
    //ForwardReferenceList* classContent,
    clang::DeclContext* clangContext,
    //clang::ASTContext* astContext,
    clang::Sema* sema,
    clang::Scope* scope,
    clang::CompilerInstance& compilerInstance,
    clang::ASTConsumer* consumer);

  virtual void parseGhostStatement(
    clang::DeclContext* clangContext,
    clang::Sema* sema,
    clang::Scope* scope,
    clang::CompilerInstance& compilerInstance,
    clang::ASTConsumer* consumer);

  virtual void parseCodeAnnotation(ForwardReferenceList& codeContainer,
    const clang::DeclContext* clangContext, clang::ASTContext* astContext,
    clang::Sema* sema, clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable, location loc);

  virtual /* code_annotation */ list parseLoopAnnotation(
    const clang::DeclContext* clangContext, clang::ASTContext* astContext,
    clang::Sema* sema, clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable, location loc);

  virtual void parseStatementAnnotation(ForwardReferenceList& codeContainer,
    const clang::DeclContext* clangContext, clang::ASTContext* astContext,
    clang::Sema* sema, clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable);

  virtual void parseFunctionContract(option& /* function_contract */ contract,
    const clang::DeclContext* clangContext, clang::ASTContext* astContext,
    clang::Sema* sema, clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable);

private:
  void initFrom(const clang::Sema* sema);

}; 

#endif
