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
//   Definition of virtual annotation comments.
//

#ifndef Annotation_CommentH
#define Annotation_CommentH

#include "Clang_utils.h"
#include "clang/Frontend/CompilerInstance.h"

namespace clang {

class DeclContext;
class ASTContext;
class Sema;
class Scope;

}

class RTTITable;

/*! @class AnnotationComment
 *  @brief An AnnotationComment object is stored each time the preprocessor
 *    encounters a comment that is valid (see the method isValid) as an
 *    annotation comment. This comment is then visited by the
 *    FramaCIRGenAction::Visitor and it is parsed at that time to produce valid
 *    annotations in the CIL AST.
 *
 *  clang provides a method <tt>clang::Preprocessor::addCommentHandler</tt>
 *    to register an instance of FramaCIRGenAction::AnnotationCommentHandler
 *    that carries the Annotation comment detection mechanism. This 
 *    FramaCIRGenAction::AnnotationCommentHandler also attaches the comment to
 *    the global context, the next declaration context, the between two
 *    instructions context, depending on the first words of the annotation. The
 *    location _range enables to precisely locate the annotation. \n
 *  When the visitor FramaCIRGenAction::Visitor looks at a declaration or at
 *    an instruction, it looks if there exist annotations between this
 *    declaration and the location of the previous declaration. If this is the
 *    case, then the declaration is parsed with the Acsl::Parser::parse method.
 *  @sa{ clang::Preprocessor::addCommentHandler,
 *       FramaCIRGenAction::AnnotationCommentHandler,
 *       FramaCIRGenAction::Visitor
 *     }
 */
class AnnotationComment {
public:
  enum Kind { KUndefined, KGhost, KGlobal, KNext, KNextStatement, 
              KNextLoop, KLabel, KOuterLoop };

protected:
  clang::SourceRange _range; //!< Precise location of the comment.
  Kind _kind;
    /*!< Attachment information for the comment.
     * This field is set up by the constructor
     * <tt>AnnotationComment::AnnotationComment(const clang::SourceManager&,
     *   clang::SourceRange)</tt>.
     */

  // A StringRef seems to be sufficient (see the implementation of RawComment
  //   for DOxygen), but as we don't want to make any assumption of the
  //   lifetime of the lexing support we prefer to perform a copy of the
  //   comment during the parsing phase, for it to be useable by visitor
  //   FramaCIRGenAction::Visitor.
  std::string* _commentText; //!< Content of the comment.
  clang::SourceLocation _commentTextLocation; //!< Location of the beginning of the comment text (without comment markers)
  bool _isLineComment;

public:
  AnnotationComment(const clang::SourceRange& range)
    : _range(range), _kind(KUndefined), _commentText(NULL),
      _isLineComment(false) {}
  AnnotationComment(const AnnotationComment& source)  // FIXME - replicated pointer to comment text
    : _range(source._range), _kind(source._kind),
      _commentText(source._commentText), _isLineComment(source._isLineComment)
    {}
  virtual ~AnnotationComment() {}

  void freeContent()
    { if (_commentText) { delete _commentText; _commentText = NULL; } }
  const std::string& getContent()
    { assert(_commentText); return *_commentText; }
  Kind getKind() const { return _kind; }

  const clang::SourceRange& getSourceRange() const { return _range; }
  clang::SourceLocation getSourceLocation() const { return _commentTextLocation; }

  bool isValid() const { return _commentText != NULL; }
  bool isGhost () const { return _kind == KGhost; }
  bool isGlobal() const { return _kind == KGlobal; }
  bool isNext() const { return _kind >= KNext && _kind <= KNextLoop; }
  bool isNextContract() const { return _kind == KNext; }
  bool isNextLoop() const { return _kind == KNextLoop; }
  bool isNextStatement() const { return _kind == KNext; }
  bool isLabel() const { return _kind == KLabel; }
  bool isOuterLoop() const { return _kind == KOuterLoop; }
  bool isLineComment() const { return _isLineComment; }

  virtual void parseGhostGlobal(
    //ForwardReferenceList& globals,
    //ForwardReferenceList* classContent,
    clang::DeclContext* clangContext,
    //clang::ASTContext* astContext,
    clang::Sema* sema,
    clang::Scope* scope,
    clang::CompilerInstance& compilerInstance,
    clang::ASTConsumer* consumer) {assert(0);}
  virtual void parseGhostStatement(
    clang::DeclContext* clangContext,
    clang::Sema* sema,
    clang::Scope* scope,
    clang::CompilerInstance& compilerInstance,
    clang::ASTConsumer* consumer) {assert(0);}
  virtual void parseGlobal(ForwardReferenceList& globals,
    ForwardReferenceList* classContent, const clang::DeclContext* clangContext,
    clang::ASTContext* astContext, clang::Sema* sema,
    clang::Scope* scope, Clang_utils* clangUtils, const RTTITable& rttiTable,
    location loc) {assert(0);}
  virtual void parseCodeAnnotation(ForwardReferenceList& codeContainer,
    const clang::DeclContext* clangContext, clang::ASTContext* astContext,
    clang::Sema* sema, clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable, location loc) {assert(0);}
  virtual /* code_annotation */ list parseLoopAnnotation(
    const clang::DeclContext* clangContext, clang::ASTContext* astContext,
    clang::Sema* sema, clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable, location loc) { assert(0); return NULL; }
  virtual void parseStatementAnnotation(ForwardReferenceList& codeContainer,
    const clang::DeclContext* clangContext, clang::ASTContext* astContext,
    clang::Sema* sema, clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable) {assert(0);}
  virtual void parseFunctionContract(option& /* function_contract */ contract,
    const clang::DeclContext* clangContext, clang::ASTContext* astContext,
    clang::Sema* sema, clang::Scope* scope, Clang_utils* clangUtils,
    const RTTITable& rttiTable) {assert(0);}
  virtual Kind getAnnotationKind(const std::string& text, clang::SourceLocation clangLocation, const clang::Sema* sema) const
    { assert(0); return KUndefined; }

  //! checks annotation for improper use of preprocessor direcctives, returns true if errors found
  virtual bool checkAnnotation(const std::string& text, clang::SourceLocation clangLocation, const clang::Sema* sema, std::string& revised) const {
    return true;
  }
}; 


class AnnotationCommentFactory {
public:
  static AnnotationComment* createAnnotationComment(
      const clang::SourceManager& sourceMgr, const clang::SourceRange& range, const clang::Sema* sema);
};

#endif
