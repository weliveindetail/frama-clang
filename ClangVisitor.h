/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-Clang                                      */
/*                                                                        */
/*  Copyright (C) 2012-2021                                               */
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

#ifndef CLANG_VisitorH
#define CLANG_VisitorH

#include "clang/Frontend/FrontendAction.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/Sema.h"
#include "clang/Sema/Scope.h"

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Comment.h"
#include "clang/AST/ASTConsumer.h"

#include "clang/Basic/Builtins.h"
#include "clang/Lex/Preprocessor.h"

#include "AnnotationComment.h"
#include "Clang_utils.h"
#include "RTTITable.h"
#include "VisitTable.h"

namespace clang {

template<>
class BeforeThanCompare<AnnotationComment> {
  const SourceManager &SM;

public:
  explicit BeforeThanCompare(const SourceManager &SM) : SM(SM) { }

  bool operator()(const AnnotationComment *LHS, const AnnotationComment *RHS)
    { return SM.isBeforeInTranslationUnit(LHS->getSourceRange().getBegin(),
          RHS->getSourceRange().getBegin());
    }
};

} // end of namespace clang

/*! @class Visitor
 *  @brief The class Visitor visits the full clang AST and during its visit
 *  it generates the CIL AST.
 *  
 *  The main methods are VisitNamedDecl, VisitFunctionDecl,
 *    VisitNamespaceDecl, VisitEnumDecl, VisitRecordDecl,
 *    VisitTypedefNameDecl, VisitFieldDecl, VisitVarDecl.
 */
class FramacVisitor;

/*! @class AnnotationCommentList
 *  @brief List of AnnotationComment comments, sorted by location.
 *
 *  The sorting property is ensured by the preprocessor.
 */
class AnnotationCommentList : public std::vector<AnnotationComment*> {
public:
  AnnotationCommentList() {}
  ~AnnotationCommentList()
    { iterator iterEnd = end();
      for (iterator iter = begin(); iter != iterEnd; ++iter) {
        (*iter)->freeContent();
        delete *iter;
      };
    }
  void add(AnnotationComment* RC, clang::SourceManager &sourceManager);
};

/*! @class FramaCIRGenAction
 *  @brief Parsing action triggered when a translation unit is parsed.
 *  
 *  This action generates the full CIL AST by registrating a Visitor in the
 *  virtual CreateASTConsumer method.
 */
class FramaCIRGenAction : public clang::ASTFrontendAction {
private:
  FILE* _outFile;
  clang::CompilerInstance& _compilerInstance;
  bool _annotError;
  bool _doesGenerateImplicitMethods;
  bool _doesGenerateBareFunctions;
  bool _isVerbose;

  static bool isAtTopNamespace(const clang::DeclContext* ctx);

public:
  void setAnnotError() { _annotError = true; }
  void setGenerateImplicitMethods() { _doesGenerateImplicitMethods = true; }
  void setGenerateBareFunctions() { _doesGenerateBareFunctions = true; }
  void setVerbose() { _isVerbose = true; }

  FramaCIRGenAction(const std::string& outputFile,
      clang::CompilerInstance& compilerInstance)
    : _outFile(NULL), _compilerInstance(compilerInstance), _annotError(false),
      _doesGenerateImplicitMethods(false), _doesGenerateBareFunctions(false),
      _isVerbose(false)
    { _outFile=fopen(outputFile.c_str(),"w");
      if (!_outFile) {
        std::cerr << "cannot open " << outputFile << " for writing\nAborting";
        exit(2);
      }
    }
  ~FramaCIRGenAction() override
    { if (fclose(_outFile)==EOF) {
        std::cerr << "error closing output file.\n";
      };
    }
  std::unique_ptr<clang::ASTConsumer>
    CreateASTConsumer(clang::CompilerInstance& CI, clang::StringRef InFile) override;

protected:
 
  // TODO: How many of these classes should be nested in FramacVisitor
  // rather than here?

  /*! @class LocalDeclContext
   *  @brief clang namespace or class declaration.
   *  
   *  class shared by LexicalLocalDeclContext and SemanticDeclContext.
   */
  class LocalDeclContext;

  /*! @class LexicalLocalDeclContext
   *  @brief lexical clang namespace or class declaration.
   *  
   *  This class is embedded as a stack element in DeclContext.
   *  It manages the entrance and the exit of namespaces/classes
   *    and is driven by clang::Decl::getLexicalParent().
   *  For a class definition only one entry/exit should occur
   *    by translation unit.
   */
  class LexicalLocalDeclContext;

  /*! @class SemanticLocalDeclContext
   *  @brief semantic clang namespace or class declaration.
   *  
   *  This class is embedded as a stack element in DeclContext.
   *  It manages the template specialization arguments and the scope
   *    of namespaces/classes. It is driven by clang::Decl::getDeclContext()
   *    and clang::DeclContext::getParent().
   *  For a class definition multiple entry/exit may occur by translation unit.
   */
  class SemanticLocalDeclContext;

  /*! @class DeclContext
   *  @brief clang Declarative context that follows the visit of _visitor.
   *  
   *  This class provides the good namespace/class encapsulation for the logic
   *    side.
   */
  class DeclContext;

  class ExpressionGuard;

  /*! @class AnnotationCommentHandler
   *  @brief Class used to create the comments to be parsed.
   *  
   *  The method HandleComment creates an AnnotationComment and registers it in
   *    _visitor._annotationCommentList. It is called by the preprocessor when
   *    it encounters a comment.
   */
  class AnnotationCommentHandler;

  class LoopAnnotationOption;
  class InstanceContexts;
  class UnvisitedNameRegistration;
  class UnvisitedRegistration;
  class VerifyNameRegistration;

  class ImmediateGlobalDependency;

  friend class FramacVisitor;
};

/*! @class LocalDeclContext
 *  @brief clang namespace or class declaration.
 *  
 *  Class shared by LexicalLocalDeclContext and SemanticDeclContext.
 *  This class is embedded as a stack in DeclContext.
 *
 */

class FramaCIRGenAction::LocalDeclContext {
protected:
  enum Tag { TUndefined, TNamespace, TClass, TLocalNamespace, TLocalClass };

private:
  Tag _tag;
  const clang::DeclContext* _synchro;

protected:
  LocalDeclContext(Tag tag, const clang::DeclContext* synchro)
    : _tag(tag), _synchro(synchro) {}
  Tag getTag() const { return _tag; }

public:
  LocalDeclContext() : _tag(TUndefined), _synchro(NULL) {}
  LocalDeclContext(const LocalDeclContext& source)
    : _tag(source._tag), _synchro(source._synchro)
    { const_cast<LocalDeclContext&>(source)._tag = TUndefined; }

  void clear()
    { _tag = TUndefined; _synchro = NULL; }
  void setClass(const clang::DeclContext* synchro)
    { assert(!_tag); _tag = TClass; _synchro = synchro; }
  void setLocalClass(const clang::DeclContext* synchro)
    { assert(!_tag); _tag = TLocalClass; _synchro = synchro; }
  void setNamespace(const clang::DeclContext* synchro)
    { assert(!_tag); _tag = TNamespace; _synchro = synchro; }
  void resetNamespace(const clang::DeclContext* synchro)
    { _tag = TNamespace; _synchro = synchro; }
  void setLocalNamespace(const clang::DeclContext* synchro)
    { assert(!_tag); _tag = TLocalNamespace; _synchro = synchro; }
  bool hasLocalContext(const clang::DeclContext* decl) const
    { return _tag >= TLocalNamespace && _synchro == decl; }
  bool isValid() const { return _tag != TUndefined; }

  bool isClass() const
    { assert(_tag); return _tag == TClass || _tag == TLocalClass; }
  bool isLocalClass() const
    { assert(_tag); return _tag == TLocalClass; }
  bool isNamespace() const
    { assert(_tag); return _tag == TNamespace || _tag == TLocalNamespace; }
  const clang::DeclContext* getSynchro() const { return _synchro; }
};

/*! @class LexicalLocalDeclContext
 *  @brief lexical clang namespace or class declaration.
 *  
 *  This class is embedded as a stack element in DeclContext.
 *  It manages the entrance and the exit of namespaces/classes
 *    and is driven by clang::Decl::getLexicalParent().
 *  For a class definition only one entry/exit should occur
 *    by translation unit.
 */

class FramaCIRGenAction::LexicalLocalDeclContext : public LocalDeclContext {
private:
  ForwardListOption /* translation_unit_decl | class_decl */ _declarations;

  LexicalLocalDeclContext(Tag tag, ForwardListOption declarations,
      const clang::DeclContext* synchro)
    : LocalDeclContext(tag, synchro), _declarations(declarations) {}

public:
  LexicalLocalDeclContext() : _declarations() {}
  LexicalLocalDeclContext(const LexicalLocalDeclContext& source)
    : LocalDeclContext(source), _declarations(source._declarations) {}

  void clear()
    { LocalDeclContext::clear(); _declarations = ForwardListOption(); }
  void setClass(option& declarations, const clang::DeclContext* synchro)
    { LocalDeclContext::setClass(synchro);
      _declarations = ForwardListOption(declarations);
    }
  void setTemplateClass(const clang::DeclContext* synchro)
    { LocalDeclContext::setClass(synchro);
      _declarations = ForwardListOption();
    }
  void setLocalClass(const clang::DeclContext* synchro)
    { // assert(false);
      LocalDeclContext::setLocalClass(synchro);
      _declarations = ForwardListOption();
    }
  void setNamespace(list& declarations, const clang::DeclContext* synchro)
    { LocalDeclContext::setNamespace(synchro);
      _declarations = ForwardListOption(declarations);
    }
  void resetNamespace(list& declarations, const clang::DeclContext* synchro)
    { LocalDeclContext::resetNamespace(synchro);
      _declarations = ForwardListOption(declarations);
    }
  void setLocalNamespace(const clang::DeclContext* synchro)
    { assert(false);
      LocalDeclContext::setLocalNamespace(synchro);
      _declarations = ForwardListOption();
    }
  ForwardReferenceList& getDeclarations()
    { return _declarations.getList(); }
  ForwardReferenceList* getDeclList(/* class_decl */ list* decllist)
    { return (isClass() && _declarations.getCList().isValid()
          && &_declarations.getCList().getFront()==decllist)
            ? &_declarations.getList() : NULL;
    }
  ForwardReferenceList& getClassContent()
    { assert(isClass()); return _declarations.getList(); }
  ForwardReferenceList& getNamespaceContent()
    { assert(isNamespace()); return _declarations.getList(); }
  void addClass(class_decl decl)
    { assert(isClass());
      _declarations.insertContainer(decl);
    }
  void addNamespace(translation_unit_decl decl,
      /* translation_unit_decl */ list** place = NULL)
    { assert(isNamespace());
      if (place)
        *place = _declarations.getCList().getBack()
            ? &_declarations.getCList().getBack()->next
            : &_declarations.getCList().getFront();
      _declarations.insertContainer(decl); 
    }
  /* translation_unit_decl */ list* getNamespacePlace() const
    { assert(isNamespace());
      return _declarations.getCList().getBack()
        ? &_declarations.getCList().getBack()->next
        : &_declarations.getCList().getFront();
    }
};
 
class FramaCIRGenAction::ImmediateGlobalDependency {
public:
  typedef
    std::pair<const clang::NamespaceDecl*, /* translation_unit_decl */ list*>
    NamespacePlace;
  typedef std::vector<NamespacePlace> NamespaceContext;

private:
  class PlaceForDeclGeneration {
  private:
    const clang::RecordDecl* _waitedClassDecl;
    const clang::RecordDecl* _originDerivedClass;
    NamespaceContext _namespaceContext;
    list* _place;
    list _nextPlace;

  public:
    PlaceForDeclGeneration()
      : _waitedClassDecl(NULL), _originDerivedClass(NULL), _place(NULL),
        _nextPlace(NULL) {}
    PlaceForDeclGeneration(const clang::RecordDecl* waitedClassDecl,
        const clang::RecordDecl* originDerivedClass,
        const std::list<LexicalLocalDeclContext>* namespaceContext,
        list* place)
      : _waitedClassDecl(waitedClassDecl),
        _originDerivedClass(originDerivedClass), _place(place)
      { if (namespaceContext) {
          std::list<LexicalLocalDeclContext>::const_iterator
            iterEnd = namespaceContext->end(), iter;
          for (iter = namespaceContext->begin(); iter != iterEnd; ++iter) {
            assert(llvm::dyn_cast<clang::NamespaceDecl>(iter->getSynchro()));
            _namespaceContext.push_back(std::make_pair(
                static_cast<const clang::NamespaceDecl*>(iter->getSynchro()),
                iter->getNamespacePlace()));
          };
        }
      }

    const clang::RecordDecl* getClassDecl() const { return _waitedClassDecl; }
    const clang::RecordDecl* getOriginClassDecl() const
      { return _originDerivedClass; }
    const NamespaceContext& getNamespaceContext() const
      { return _namespaceContext; }
    list* getPlace() const { return _place; }
    void setNextPlace() { assert(_place); _nextPlace = *_place; }
    void adjustPlace()
      { assert(_place);
        if (_nextPlace) {
          assert(*_place);
          while (*_place != _nextPlace) {
            _place = &(*_place)->next;
            assert(*_place);
          };
        };
      }
  };
  
  std::vector<PlaceForDeclGeneration> _placesForDecl;

public:
  ImmediateGlobalDependency() {}

  void addDeclarationPlace(const clang::RecordDecl* decl,
      const clang::RecordDecl* originDecl,
      const std::list<LexicalLocalDeclContext>* currentContext,
      /* translation_unit_decl */ list* place)
    { _placesForDecl.push_back(PlaceForDeclGeneration(decl, originDecl,
          currentContext, place));
    }
  bool isEmpty() const { return _placesForDecl.empty(); }
  bool globalInsertIfBooked(const clang::RecordDecl* decl,
      const std::list<LexicalLocalDeclContext>* context,
      translation_unit_decl globalDecl,
      /* translation_unit_decl */ list*& insertionPlace,
      bool isInClass, const FramacVisitor& visitor);
  bool hasGlobalBooked(const clang::RecordDecl* decl) const;
  /* translation_unit_decl */ list* adjustBeforePlace(
    const clang::RecordDecl* decl);

  void makeTemporaryDependentUnvisited(const clang::RecordDecl* baseClass,
      VisitTable& visitTable);
  void makeTemporaryDependentVisited(const clang::RecordDecl* baseClass,
      VisitTable& visitTable, ForwardReferenceList& globals);
};

/*! @class SemanticLocalDeclContext
 *  @brief semantic clang namespace or class declaration.
 *  
 *  This class is embedded as a stack element in DeclContext.
 *  It manages the template specialization arguments and the scope
 *    of namespaces/classes. It is driven by clang::Decl::getDeclContext()
 *    and clang::DeclContext::getParent().
 *  For a class definition multiple entry/exit may occur by translation unit.
 */

class FramaCIRGenAction::SemanticLocalDeclContext : public LocalDeclContext {
private:
  SemanticLocalDeclContext(Tag tag, const clang::DeclContext* synchro)
    : LocalDeclContext(tag, synchro) {}

public:
  SemanticLocalDeclContext() {}
  SemanticLocalDeclContext(const LocalDeclContext& source)
    : LocalDeclContext(source) {}
  SemanticLocalDeclContext findDecl(const clang::DeclContext* subDecl) const
    { Tag tagSubDecl = subDecl->isNamespace() ? TNamespace
          : (subDecl->isRecord() ? TClass : TUndefined);
      return SemanticLocalDeclContext(tagSubDecl, subDecl);
    }
};

/*! @class DeclContext
 *  @brief clang Declarative context that follows the visit of _visitor.
 *  
 *  This class provides the good namespace/class encapsulation for the logic
 *    side.
 */
class FramaCIRGenAction::DeclContext {
private:
  clang::DiagnosticsEngine& _diags;
  std::list<LexicalLocalDeclContext> _lexicalParent;
  std::list<SemanticLocalDeclContext> _semanticParent;
  clang::ASTContext* _context;
  clang::Sema* _sema;
  clang::Scope* _scope; // follow _semanticParent
  int _localPush;
  clang::FunctionDecl* _currentFunctionBody;
  // int _templateContextsNumber;
  // bool _doesVisitInstances;

public:
  DeclContext(clang::DiagnosticsEngine& Diags)
    : _diags(Diags), _context(NULL), _sema(NULL), _scope(NULL),
      _localPush(0), _currentFunctionBody(NULL) /*, _templateContextsNumber(0),
      _doesVisitInstances(false) */{}

  clang::DiagnosticsEngine& getDiagnosticEngine() const { return _diags; }
  void parseGhostStatement(
      AnnotationComment& comment,
      const clang::DeclContext* clangContext,
      ForwardReferenceList* container);
  void parseGhostGlobal(
      AnnotationComment& comment,
      const clang::DeclContext* clangContext);
  void setTranlationUnit(clang::ASTContext& context, clang::Sema& sema)
    { _context = &context; _sema = &sema;
      _scope = _sema->getScopeForContext(context.getTranslationUnitDecl());
    }
  bool hasLexicalContext() const { return !_lexicalParent.empty(); }
  bool isSemanticLocalClass() const
    { return !_semanticParent.empty() && _semanticParent.back().isLocalClass();
    }
  bool isClass() const
    { return !_lexicalParent.empty() && _lexicalParent.back().isClass(); }
  bool isNamespace() const
    { return !_lexicalParent.empty() && _lexicalParent.back().isNamespace(); }
  void add(class_decl decl)
    { assert(!_lexicalParent.empty()); _lexicalParent.back().addClass(decl); }
  void add(translation_unit_decl decl,
      /* translation_unit_decl */ list** place = NULL)
    { assert(!_lexicalParent.empty());
      _lexicalParent.back().addNamespace(decl, place);
    }
  void reopenLexicalHierarchy(FramacVisitor& visitor);
  ForwardReferenceList& getClassContent()
    { assert(!_lexicalParent.empty());
      return _lexicalParent.back().getClassContent();
    }
  ForwardReferenceList& getNamespaceContent()
    { assert(!_lexicalParent.empty());
      return _lexicalParent.back().getNamespaceContent();
    }
  ForwardReferenceList* getDeclList(/* class_decl */ list* decllist)
    { std::list<LexicalLocalDeclContext>::reverse_iterator
        iterEnd = _lexicalParent.rend(),
        iter = _lexicalParent.rbegin();
      ForwardReferenceList* result = NULL;
      while (!result && iter != iterEnd) {
        result = iter->getDeclList(decllist);
        ++iter;
      };
      return result;
    }

  void pushClass(option& declarations, const clang::DeclContext* synchro);
  void pushLexicalLocalClass(const clang::DeclContext* synchro);
  void pushSemanticLocalClass(const clang::DeclContext* synchro);
  void pushTemplateClass(const clang::DeclContext* synchro);
  void pushSemanticLocalTemplateClass(const clang::DeclContext* synchro);
  void pushNamespace(list& declarations, const clang::DeclContext* synchro);
  void pushSemanticLocalNamespace(const clang::DeclContext* synchro);
  bool hasLexicalLocalContext(const clang::DeclContext* decl) const
    { return !_lexicalParent.empty()
        && _lexicalParent.back().hasLocalContext(decl);
    }
  bool hasSemanticLocalContext(const clang::DeclContext* decl) const
    { return !_semanticParent.empty()
        && _semanticParent.back().hasLocalContext(decl);
    }

  void pushCompoundScope() {
#if CLANG_VERSION_MAJOR < 7
    _sema->PushCompoundScope();
#else
    _sema->PushCompoundScope(false);
#endif
  }

  void pop();
  void pushFunctionBody(clang::FunctionDecl* functionDecl);
  void pushBlock();
  void popBlock();
  void addDecl(clang::Decl *decl);
  // void removeDecl(clang::Decl *decl)
  //   { assert(_scope); _scope->RemoveDecl(decl); }
  void popFunctionBody(clang::FunctionDecl* functionDecl);
  clang::FunctionDecl* getSFunctionDecl() const { return _currentFunctionBody; }

  void lexicalSynchronizeWith(const clang::DeclContext* parentDecl,
      FramacVisitor& visitor);
  void semanticSynchronizeWith(const clang::DeclContext* parentDecl,
      FramacVisitor& visitor);
  void clearLexical(FramacVisitor& visitor);
  void clearSemantic(FramacVisitor& visitor);
  void clear(FramacVisitor& visitor)
    { clearSemantic(visitor);
      clearLexical(visitor);
    }
  void setLocalPush(const clang::DeclContext* parentDecl);
  // void setLocalPushInstantiation(option& declarations,
  //     const clang::DeclContext* classContext);

  void clearLocalPush();
  clang::Scope* getScope() const { return _scope; }
  // void pushTemplateContext() { ++_templateContextsNumber; }
  // void popTemplateContext()
  //   { assert(_templateContextsNumber > 0);
  //     --_templateContextsNumber;
  //     _doesVisitInstances = false;
  //   }
  // bool hasTemplateContext() const
  //   { return !_doesVisitInstances && _templateContextsNumber > 0; }
  // void setVisitInstances() { _doesVisitInstances = true; }
  // void clearVisitInstances() { _doesVisitInstances = false; }

  const std::list<LexicalLocalDeclContext>& getLexicalParent() const
    { return _lexicalParent; }
  const clang::DeclContext* getSemanticParentContext() const
    { return !_semanticParent.empty()
          ? _semanticParent.back().getSynchro() : NULL;
    }
};

inline void
FramaCIRGenAction::DeclContext::pushClass(option& declarations,
    const clang::DeclContext* synchro)
{ _lexicalParent.push_back(LexicalLocalDeclContext());
  _lexicalParent.back().setClass(declarations, synchro);
  _semanticParent.push_back(SemanticLocalDeclContext());
  _semanticParent.back().setClass(synchro);
  clang::Scope* scope = new clang::Scope(_scope, 0, _diags);
  _scope = scope;
  _sema->EnterDeclaratorContext(_scope,
      const_cast<clang::DeclContext*>(synchro));
}

inline void
FramaCIRGenAction::DeclContext::pushLexicalLocalClass(
    const clang::DeclContext* synchro)
{ _lexicalParent.push_back(LexicalLocalDeclContext());
  _lexicalParent.back().setLocalClass(synchro);
}

inline void
FramaCIRGenAction::DeclContext::pushSemanticLocalClass(
    const clang::DeclContext* synchro)
{ _semanticParent.push_back(SemanticLocalDeclContext());
  _semanticParent.back().setLocalClass(synchro);
  clang::Scope* scope = new clang::Scope(_scope, 0, _diags);
  _scope = scope;
  _sema->EnterDeclaratorContext(_scope,
      const_cast<clang::DeclContext*>(synchro));
}

inline void
FramaCIRGenAction::DeclContext::pushTemplateClass(
    const clang::DeclContext* synchro)
{ _lexicalParent.push_back(LexicalLocalDeclContext());
  _lexicalParent.back().setTemplateClass(synchro);
  _semanticParent.push_back(SemanticLocalDeclContext());
  _semanticParent.back().setClass(synchro);
  clang::Scope* scope = new clang::Scope(_scope, 0, _diags);
  _scope = scope;
  _sema->EnterDeclaratorContext(_scope,
      const_cast<clang::DeclContext*>(synchro));
  // pushTemplateContext();
}

inline void
FramaCIRGenAction::DeclContext::pushSemanticLocalTemplateClass(
    const clang::DeclContext* synchro)
{ _semanticParent.push_back(SemanticLocalDeclContext());
  _semanticParent.back().setLocalClass(synchro);
  clang::Scope* scope = new clang::Scope(_scope, 0, _diags);
  _scope = scope;
  _sema->EnterDeclaratorContext(_scope,
      const_cast<clang::DeclContext*>(synchro));
  // pushTemplateContext();
}

inline void
FramaCIRGenAction::DeclContext::pushNamespace(list& declarations,
    const clang::DeclContext* synchro)
{ _lexicalParent.push_back(LexicalLocalDeclContext());
  _lexicalParent.back().setNamespace(declarations, synchro);
  _semanticParent.push_back(SemanticLocalDeclContext());
  _semanticParent.back().setNamespace(synchro);
  clang::Scope* scope = new clang::Scope(_scope, 0, _diags);
  _scope = scope;
  _sema->EnterDeclaratorContext(_scope,
      const_cast<clang::DeclContext*>(synchro));
}

inline void
FramaCIRGenAction::DeclContext::pushSemanticLocalNamespace(
    const clang::DeclContext* synchro)
{ _semanticParent.push_back(SemanticLocalDeclContext());
  _semanticParent.back().setLocalNamespace(synchro);
  clang::Scope* scope = new clang::Scope(_scope, 0, _diags);
  _scope = scope;
  _sema->EnterDeclaratorContext(_scope,
      const_cast<clang::DeclContext*>(synchro));
}

inline void
FramaCIRGenAction::DeclContext::pop()
{ clang::Scope* scope = _scope->getParent();
  _sema->ExitDeclaratorContext(_scope);
  assert(scope);
  delete _scope;
  _scope = scope;
  _semanticParent.pop_back();
  _lexicalParent.pop_back();
}

inline void
FramaCIRGenAction::DeclContext::pushBlock()
{ clang::Scope* scope = new clang::Scope(_scope, 0, _diags);
  _scope = scope;
  pushCompoundScope();
}

inline void
FramaCIRGenAction::DeclContext::popBlock()
{ clang::Scope* scope = _scope->getParent();
  _sema->PopCompoundScope();
  assert(scope);
  delete _scope;
  _scope = scope;
}

inline void
FramaCIRGenAction::DeclContext::addDecl(clang::Decl *decl)
{ assert(_scope);
  clang::Decl::Kind kind = decl->getKind();
  if (kind >= clang::Decl::firstNamed && kind <= clang::Decl::lastNamed) {
    assert(llvm::dyn_cast<clang::NamedDecl>(decl));
    // clang::Token identifierToken;
    // identifierToken.startToken();
    // identifierToken.clearFlag(Token::NeedsCleaning);
    // identifierToken.setIdentifierInfo(0);
    // // std::memset(&identifierToken, 0, sizeof(clang::Token));
    // identifierToken.setLength(name.size());
    // // identifierToken.setLocation(getSourceLocation(BufferPtr,
    // //     TokLen));
    // identifierToken.setKind(clang::tok::raw_identifier);
    // identifierToken.setRawIdentifierData(name.c_str());
    // clang::IdentifierInfo& identifierInfo = *_clangSema
    //     ->getPreprocessor().LookUpIdentifierInfo(identifierToken);
    clang::NamedDecl* namedDecl = static_cast<clang::NamedDecl*>(decl);
    // clang::IdentifierInfo& identifierInfo
    //    = _sema->getPreprocessor().getIdentifierTable()
    //       .get(namedDecl->getName());
    // identifierInfo.setFETokenInfo(decl);
    if (namedDecl->getName().size() > 0)
      _sema->PushOnScopeChains(namedDecl, _scope, false);
    else
      _scope->AddDecl(decl);
  }
  else
    _scope->AddDecl(decl);
}

/*! @class AnnotationCommentHandler
 *  @brief register comments for their future ACSL parsing
 */

class FramaCIRGenAction::AnnotationCommentHandler
    : public clang::CommentHandler {
private:
  clang::CompilerInstance& _compilerInstance;
  FramacVisitor& _visitor;
  clang::Sema* _sema;
  clang::SourceManager* _sourceManager;

public:
  AnnotationCommentHandler(clang::CompilerInstance& compilerInstance,
      FramacVisitor& visitor)
    : _compilerInstance(compilerInstance), _visitor(visitor),
      _sema(NULL), _sourceManager(NULL) {}

  clang::CompilerInstance& compilerInstance() const
    { return _compilerInstance; }
  bool HandleComment(clang::Preprocessor &PP,
      clang::SourceRange Comment) override;
};

/*! @class LoopAnnotationOption
 *  @brief optional loop annotation with explicit destruction.
 */

class FramaCIRGenAction::LoopAnnotationOption {
private:
  /* code_annotation */ list _annotationsList;
  const clang::Stmt* _attachedLoop;

public:
  LoopAnnotationOption() : _annotationsList(NULL), _attachedLoop(NULL) {}
  ~LoopAnnotationOption()
    { while (_annotationsList) {
        free_code_annotation((code_annotation) _annotationsList
            ->element.container);
        list temp = _annotationsList;
        _annotationsList = _annotationsList->next;
        free(temp);
      };
    }

  void setAnnotation(const clang::Stmt* attachedLoop,
      /* code_annotation */ list annotationsList)
    { assert(!_attachedLoop);
      _attachedLoop = attachedLoop;
      _annotationsList = annotationsList;
    }
  void attachTo(const clang::Stmt* stmt, statement loopStatement)
    { if (_attachedLoop) {
        assert(_attachedLoop == stmt);
        if (loopStatement->tag_statement == FOR)
          loopStatement->cons_statement.For.annot = _annotationsList;
        else if (loopStatement->tag_statement == WHILE)
          loopStatement->cons_statement.While.annot = _annotationsList;
        else if (loopStatement->tag_statement == DOWHILE)
          loopStatement->cons_statement.DoWhile.annot = _annotationsList;
        else
          assert(false);
        _annotationsList = NULL;
        _attachedLoop = NULL;
      };
    }
};

class FramaCIRGenAction::InstanceContexts {
public:
  typedef std::vector<const clang::Decl*> UnvisitedDecls;

private:
  union LocalContext {
    VisitTable::MissingClassGeneration* classContent;
    VisitTable::MissingSubClassGeneration* subclassContent;

    LocalContext() { classContent = NULL; }
    LocalContext(VisitTable::MissingClassGeneration* content)
      { classContent = content; }
    LocalContext(VisitTable::MissingSubClassGeneration* content)
      { subclassContent = content; }
    LocalContext(const LocalContext& source)
      { memcpy(this, &source, sizeof(LocalContext)); }

    LocalContext& operator=(const LocalContext& source)
      { memcpy(this, &source, sizeof(LocalContext)); return *this; }
  }; // MissingClassGeneration or MissingSubClassGeneration
  typedef std::pair<UnvisitedDecls*, UnvisitedDecls> UnvisitedBodyName;
  std::vector<std::pair<UnvisitedBodyName, LocalContext> > _currentContext;
  std::unique_ptr<std::vector<const clang::Decl*> >
    _waitDeclarationsFunctions;

public:
  InstanceContexts() {}
  void push(VisitTable::MissingClassGeneration& context)
    { assert(_currentContext.empty());
      _currentContext.push_back(std::make_pair(
          std::make_pair(&context.waitDeclarations(), UnvisitedDecls()),
          LocalContext(&context)));
    }
  void push(VisitTable::MissingSubClassGeneration& context)
    { assert(!_currentContext.empty());
      _currentContext.push_back(std::make_pair(
          std::make_pair(&context.waitDeclarations(), UnvisitedDecls()),
          LocalContext(&context)));
    }
  void pushFunction()
    { assert(!_waitDeclarationsFunctions.get());
      _waitDeclarationsFunctions.reset(new std::vector<const
        clang::Decl*>());
      _currentContext.push_back(std::make_pair(
          std::make_pair(&*_waitDeclarationsFunctions, UnvisitedDecls()),
          LocalContext()));
    }
  void popFunction(std::vector<const clang::Decl*>& waitDeclarations,
      std::vector<const clang::Decl*>& namedDeclarations)
    { assert(_waitDeclarationsFunctions.get()
          && waitDeclarations.empty());
      _currentContext.back().first.second.swap(namedDeclarations);
      _waitDeclarationsFunctions->swap(waitDeclarations);
      _waitDeclarationsFunctions.reset();
      _currentContext.pop_back();
    }
  void pop() { _currentContext.pop_back(); }
  void pop(std::vector<const clang::Decl*>& namedDeclarations)
    { _currentContext.back().first.second.swap(namedDeclarations);
      _currentContext.pop_back();
    }
  int size() const { return _currentContext.size(); }
  bool isClassContext() const { return _currentContext.size() == 1; }
  bool isSubClassContext() const { return _currentContext.size() > 1; }
  bool isEmpty() const { return _currentContext.empty(); }
  const clang::Decl* getRootDecl() const
    { assert(_currentContext.size() >= 1);
      return _currentContext.front().second.classContent->key();
    }
  UnvisitedDecls& unvisitedDecls()
    { assert(_currentContext.size() >= 1);
      return *_currentContext.back().first.first;
    }
  UnvisitedDecls& unvisitedNameDecls()
    { assert(_currentContext.size() >= 1);
      return _currentContext.back().first.second;
    }
  UnvisitedDecls& firstUnvisitedNameDecls()
    { assert(_currentContext.size() >= 1);
      return _currentContext.front().first.second;
    }
  void removeUnvisited(const clang::Decl* decl)
    { if (_currentContext.size() >= 1) {
        std::vector<std::pair<UnvisitedBodyName, LocalContext> >::iterator
          iterEnd = _currentContext.end(), iter = _currentContext.begin();
        for (; iter != iterEnd; ++iter) {
          std::vector<const clang::Decl*>& unvisited = *iter->first.first;
          int size = unvisited.size();
          for (int index = 0; index < size; ++index) {
            if (unvisited[index] == decl) {
              unvisited.erase(unvisited.begin() + index);
              --index;
              --size;
            };
          };
        };
      };
    }
  VisitTable::MissingClassGeneration& lastClassContext()
    { assert(_currentContext.size() == 1);
      return *_currentContext.back().second.classContent;
    }
  VisitTable::MissingSubClassGeneration* lastSubClassContext
      (/* class_decl */ list** parent=NULL)
    { assert(_currentContext.size() >= 1);
      VisitTable::MissingSubClassGeneration* result;
      if (_currentContext.size() == 1)
        result = NULL;
      else {
        result = _currentContext.back().second.subclassContent;
        if (parent) {
          if (_currentContext.size() == 2) {
            *parent = &_currentContext.front().second.classContent
               ->getContent();
          }
          else 
            *parent = &_currentContext[_currentContext.size()-2].second
               .subclassContent->getContent();
        };
      };
      return result;
    }
  VisitTable::MissingClassGeneration& firstClassContext()
    { assert(_currentContext.size() >= 1);
      return *_currentContext.front().second.classContent;
    }

  // for instantiation point as a inner friend class instead of an outer class
  void swap(InstanceContexts& source)
    { _currentContext.swap(source._currentContext);
      _waitDeclarationsFunctions.swap(source._waitDeclarationsFunctions);
    }
};

class FramacVisitor
  : public clang::ASTConsumer,
    public clang::RecursiveASTVisitor<FramacVisitor> {
public:
  /* the global state machine to maintain the states of the visitor with respect
       to the template/instance context, the lexical and semantic context.
  */
  enum State
    { SSynchronized, STempLexicalOut, STempSemanticOut, STempLexicalSemanticOut,
      STemplateSynchronized, STemplateTempLexicalOut,
        STemplateTempSemanticOut, STemplateTempLexicalSemanticOut,
      SInstanceSynchronized, SInstanceTempLexicalOut,
        SInstanceTempSemanticOut, SInstanceTempLexicalSemanticOut
    };

private:
  typedef clang::RecursiveASTVisitor<FramacVisitor> Parent;
  // used to factorize makeDerivedToBase between pointer and references.
  enum ptr_or_ref { PTR, REF };
  FILE* _outFile;
  clang::Sema* _sema;
  file _intermediateAST;
  ForwardDoubleReferenceList _globals;
  /* _state is an identifier for the global state in which lie the following
     fields: _parents, _templateContextsNumber, _instanceContexts
      (, _lexicalContextForPostVisit, _semanticContextForPostVisit).
  */
  FramaCIRGenAction::DeclContext _parents;
  State _state;
  clang::ASTContext* _context;
  /* _memberType is used when handling default initialization of a field
     that has brace-or-equal initializer (see 12.6.2§8). It contains the
     type of the field.
   */
  clang::Type::TypeClass _memberType;
  /* _implicitThisStar is the lvalue currently being built when translating
     an initializer. You have to explicitely use an addrOf if you want
     to take its address, e.g. to feed it to a constructor.
   */
  mutable expression _implicitThisStar;
  mutable bool _isImplicitThisBare;
  bool _ghost; /* true if we are currently in a ghost section. */
  typedef llvm::SmallPtrSet<clang::Decl*,32> ghost_set;
  ghost_set _ghost_set;
  Clang_utils* _clangUtils;
  FramaCIRGenAction::AnnotationCommentHandler _commentHandler;
  AnnotationCommentList _annotationCommentList;
  mutable int _commentIndex;
  mutable int _templateCommentIndex;
  typedef std::map<clang::Decl*, std::list<AnnotationComment*> >
      TemplatedAttachedComments;
  mutable TemplatedAttachedComments _templatedAttachedComments;
  const clang::DeclContext* _lexicalContextForPostVisit;
  const clang::DeclContext* _semanticContextForPostVisit;
  ForwardList _delayedImplementations;
  FramaCIRGenAction::LoopAnnotationOption _delayedLoopAnnotation;
  RTTITable _rttiTable;
  FramaCIRGenAction::ImmediateGlobalDependency _immediateGlobalDependency;
  static const int SizeOfBuiltinArray =
      (clang::Builtin::FirstTSBuiltin+sizeof(unsigned)*8-1)
         / (sizeof(unsigned)*8);
  qual_type _typeFunctionResult; /* for return statement */

  // array of flags indicating whether a cabs declaration has been generated
  // for a given clang builtin.
  unsigned _generatedBuiltins[SizeOfBuiltinArray];
  inline bool isGeneratedBuiltin(unsigned builtinID) {
    return
      _generatedBuiltins[builtinID/(sizeof(unsigned) * 8)]
      & (1U << (builtinID % (sizeof(unsigned) * 8)));
  }
  inline void setGeneratedBuiltin(unsigned builtinID) {
    _generatedBuiltins[builtinID/(sizeof(unsigned)*8)] |=
      (1U << (builtinID % (sizeof(unsigned) * 8)));
  }

  void addGhostDecl(clang::DeclGroupRef Decl) {
    clang::DeclGroupRef::iterator it = Decl.begin();
    clang::DeclGroupRef::iterator end = Decl.end();
    for (; it != end; it++) _ghost_set.insert(*it); 
  }

  inline location makeLocation(clang::SourceRange const& locs) const {
    return _clangUtils->makeLocation(locs);
  }
  inline location makeDeclLocation(clang::Decl const& decl) const {
    return _clangUtils->makeDeclLocation(decl);
  }

  // Don't question the choice of count as a name for a function returning
  // a boolean.
  bool isGhostDecl(clang::Decl* Decl) { return _ghost_set.count(Decl); }

  bool _generatedVaList;

  friend class FramaCIRGenAction::UnvisitedNameRegistration;
  friend class FramaCIRGenAction::UnvisitedRegistration;
  friend class FramaCIRGenAction::VerifyNameRegistration;
  friend class FramaCIRGenAction::DeclContext;
  friend class FramaCIRGenAction::ExpressionGuard;
  friend class FramaCIRGenAction::AnnotationCommentHandler;
  friend class FramaCIRGenAction::ImmediateGlobalDependency;

  int _templateContextsNumber;
  FramaCIRGenAction::InstanceContexts _instanceContexts;
  std::vector<std::pair<clang::RecordDecl*,
        FramaCIRGenAction::InstanceContexts> >
      _alternateInstanceContexts; // a stack for recursive VisitRecordDecl
  VisitTable _tableForWaitingDeclarations;
  std::set<const clang::TypedefNameDecl*> _generatedTypedefsInAdvance;
  mutable std::vector<const clang::ExprWithCleanups*> _cleanups;

  friend class AnnotationCommentHandler;

  void pushCompoundScope() {
#if CLANG_VERSION_MAJOR < 7
    _sema->PushCompoundScope();
#else
    _sema->PushCompoundScope(false);
#endif
  }

  void pushTemplateContext() { ++_templateContextsNumber; }
  void popTemplateContext()
    { assert(_templateContextsNumber > 0);
      --_templateContextsNumber;
    }
  bool hasTemplateContext() const { return _templateContextsNumber > 0; }

  void pushInstanceContext(VisitTable::MissingClassGeneration& context)
    { _instanceContexts.push(context); }
  void pushInstanceContext(VisitTable::MissingSubClassGeneration& context)
    { _instanceContexts.push(context); }
  void popInstanceContext(const clang::Decl* decl)
    { std::vector<const clang::Decl*> waitNameDeclarations;
      _instanceContexts.pop(waitNameDeclarations);
      if (!waitNameDeclarations.empty()) {
        std::vector<const clang::Decl*>::const_iterator
            iterEnd = waitNameDeclarations.end();
        for (std::vector<const clang::Decl*>::const_iterator iter
            = waitNameDeclarations.begin(); iter != iterEnd; ++iter)
          insertNamedDeclaration(*iter, true);
      };
    }
  bool hasInstanceContext() const { return _instanceContexts.size() > 0; }
  FramaCIRGenAction::InstanceContexts::UnvisitedDecls& unvisitedDecls()
    { return _instanceContexts.unvisitedDecls(); }
  FramaCIRGenAction::InstanceContexts::UnvisitedDecls& unvisitedNameDecls()
    { return _instanceContexts.unvisitedNameDecls(); }

  void pushInstanceFunction() { _instanceContexts.pushFunction(); }
  void popInstanceFunction(std::vector<const clang::Decl*>& waitDeclarations)
    { std::vector<const clang::Decl*> waitNameDeclarations;
      _instanceContexts.popFunction(waitDeclarations, waitNameDeclarations);
      if (!waitNameDeclarations.empty()) {
        std::vector<const clang::Decl*>::const_iterator
            iterEnd = waitNameDeclarations.end();
        for (std::vector<const clang::Decl*>::const_iterator iter
            = waitNameDeclarations.begin(); iter != iterEnd; ++iter)
          insertNamedDeclaration(*iter, true);
      };
    }
  // qualified_name makeQualifiedName(const clang::NamedDecl& decl) const;
  cond_statement makeCondition(const clang::VarDecl* decl, expression e,
      bool* shouldDelay=NULL);
  void makeImplicitThis(const clang::VarDecl* vdec) const;

  /// translates initialization init for the type typ.
  init_expr makeInitExpr(
    const clang::QualType& typ,
    const clang::Expr* init,
    bool* shouldDelay=NULL);

  // returns the initializer_list materialized by a std::initializer_list
  // Cf. below
  init_expr make_explicit_initializer_list(const clang::Expr* e);

  // converts an std::initializer_list<T>
  exp_node make_initializer_list(const clang::CXXStdInitializerListExpr*il);

  // finalize a call node, adding temporary or dereference when needed
  exp_node convert_result(FramaCIRGenAction::ExpressionGuard& guard,
    const clang::QualType& ret, exp_node call, const clang::Expr* expr);
  exp_node make_lambda_expr(const clang::LambdaExpr* lam);
  exp_node makeTemporaryObjectExpression(
      const clang::CXXTemporaryObjectExpr* constructor,
      bool* shouldDelay, /* statement */ list* receiver);
  exp_node makeConstructExpression(
      const clang::CXXConstructExpr* constructor,
      bool* shouldDelay, /* statement */ list* receiver,
      bool hasImplicitThis,  bool isImplicitThisBare,
      FramaCIRGenAction::ExpressionGuard& guard);
  exp_node makeDeleteExpression(const clang::CXXDeleteExpr* deleteExpr,
      bool* shouldDelay, /* statement */ list* receiver);
  exp_node makeNewExpression(const clang::CXXNewExpr* newExpr,
      bool* shouldDelay, /* statement */ list* receiver);

  // true iff the call expression invokes operator() of a lambda object
  bool is_lambda_call(const clang::CallExpr* callExpr);

  // specific translation for a call when is_lambda_call(callExpr) is true
  exp_node makeLambdaCallExpression(
    const clang::CallExpr* callExpr, bool* shouldDelay, list* receiver,
    FramaCIRGenAction::ExpressionGuard& guard);

  // general case for the translation of a call
  exp_node makeCallExpression(const clang::CallExpr* callExpr,
      bool* shouldDelay, /* statement */ list* receiver,
      FramaCIRGenAction::ExpressionGuard& guard);
  exp_node makeMemberCallExpression(const clang::CXXMemberCallExpr* callExpr,
      bool* shouldDelay, /* statement */ list* receiver,
      FramaCIRGenAction::ExpressionGuard& guard);
  exp_node makeBaseToDerivedPointerCastExpression(
      const clang::CXXRecordDecl* base, qual_type baseType,
      const clang::CXXRecordDecl* derived, qual_type derivedType,
      expression expr);
  exp_node makeBaseToDerivedReferenceCastExpression(
      const clang::CXXRecordDecl* base, qual_type baseType,
      const clang::CXXRecordDecl* derived, qual_type derivedType,
      expression expr);
  exp_node makeDerivedToBaseCastExpression(
      ptr_or_ref kind,
      const clang::CXXRecordDecl* derived, qual_type derivedType,
      const clang::CXXRecordDecl* base, expression expr, bool* shouldDelay);
  // factorization between a CastExpr of of Dynamic kind
  // and a CXXDynamicCastExpr
  exp_node makeDynamicCastExpressionAux(
    const clang::SourceLocation,
    const clang::QualType result_type,
    const clang::QualType orig_type,
    expression subExpr);
  exp_node makeCastExpression(const clang::CastExpr* castExpr,
      bool* shouldDelay, /* statement */ list* receiver,
      FramaCIRGenAction::ExpressionGuard& guard);
  exp_node makeDynamicCastExpression(const clang::CXXDynamicCastExpr* castExpr,
      bool* shouldDelay, /* statement */ list* receiver,
      FramaCIRGenAction::ExpressionGuard& guard);
  exp_node makeCompoundLiteralExpression(
      const clang::CompoundLiteralExpr* compoundExpr,
      bool* shouldDelay, /* statement */ list* receiver,
      bool hasImplicitThis, FramaCIRGenAction::ExpressionGuard& guard);
  exp_node makeDeclRefExpression(const clang::DeclRefExpr* variableExpr,
      bool* shouldDelay, /* statement */ list* receiver,
      FramaCIRGenAction::ExpressionGuard& guard);
  exp_node makeMaterializeTemporaryExpression(
      const clang::MaterializeTemporaryExpr* tmpExpr, bool* shouldDelay,
      /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard);
  exp_node makeBindTemporaryExpression(const clang::CXXBindTemporaryExpr* tmp,
      bool* shouldDelay, /* statement */ list* receiver,
      bool hasImplicitThisStar, FramaCIRGenAction::ExpressionGuard& guard);
  exp_node makeUnaryOperator(const clang::UnaryOperator* unaryExpr,
      bool* shouldDelay, /* statement */ list* receiver,
      FramaCIRGenAction::ExpressionGuard& guard);
  exp_node makeRecordInitExpression(const clang::RecordDecl& record,
      const clang::Expr* expr, expression lvalueThisStar,
      bool* shouldDelay, /* statement */ list* receiver);
  exp_node makeConstantArrayInitExpression(
      const clang::ConstantArrayType& arrayType, const clang::Expr* expr,
      expression lvalueThisStar, bool* shouldDelay,
      /* statement */ list* receiver);
  exp_node makeImplicitValueInitExpression(
      const clang::ImplicitValueInitExpr* implicit_expr, bool* shouldDelay,
      /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard,
      const clang::Type* type=NULL);
  exp_node makeUnaryExprOrTypeTraitExpression(
      const clang::UnaryExprOrTypeTraitExpr* expr, bool* shouldDelay,
      /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard);
  exp_node makeAtomicExprExpression(
    const clang::AtomicExpr* expr, bool* shouldDelay,
    /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard);

  expression getNodeReference(expression expr, const clang::QualType& type)
  { if (expr->econtent->tag_exp_node == UNARY_OPERATOR
        && expr->econtent->cons_exp_node.Unary_operator.kind
        ->tag_uokind == UOCASTDEREF) {
        expression res = expr->econtent->cons_exp_node.Unary_operator.sub;
        free_uokind(expr->econtent->cons_exp_node.Unary_operator.kind);
        free(expr->econtent);
        free(expr);
        expr = res;
      };
    if (expr->econtent->tag_exp_node == ASSIGN) {
      expression lvalue = expr->econtent->cons_exp_node.Assign.lvalue;
      expression temp_init =
        expression_cons(
          copy_loc(lvalue->eloc),
          exp_node_Address(
            expression_cons(copy_loc(lvalue->eloc), lvalue->econtent)));
        lvalue->econtent =
          exp_node_Temporary(
            mk_tmp_name(),
            qual_type_cons(
              NULL,
              typ_Pointer(
                pkind_PDataPointer(
                  makeDefaultType(
                    _clangUtils->getSourceLocation(expr->eloc), type)))),
            init_expr_Single_init(temp_init), false);

        expr=expression_cons(copy_loc(expr->eloc), exp_node_Dereference(expr));
      };
      return expr;
    }
  expression getNodeReference(expression expr, qual_type type) const
    { if (expr->econtent->tag_exp_node == UNARY_OPERATOR
          && expr->econtent->cons_exp_node.Unary_operator.kind
              ->tag_uokind == UOCASTDEREF) {
        expression res = expr->econtent->cons_exp_node.Unary_operator.sub;
        free_uokind(expr->econtent->cons_exp_node.Unary_operator.kind);
        free(expr->econtent);
        free(expr);
        expr = res;
      };
      if (expr->econtent->tag_exp_node == ASSIGN) {
        expression lvalue = expr->econtent->cons_exp_node.Assign.lvalue;
        expression temp_init = expression_cons(copy_loc(lvalue->eloc),
          exp_node_Address(expression_cons(copy_loc(lvalue->eloc),
           lvalue->econtent)));
        lvalue->econtent = exp_node_Temporary(mk_tmp_name(),
          qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
            type))), init_expr_Single_init(temp_init), false);
        expr=expression_cons(copy_loc(expr->eloc), exp_node_Dereference(expr));
      };
      return expr;
    }
  expression getNodePReference(expression expr,
      const clang::QualType& type)
    { if (expr->econtent->tag_exp_node == UNARY_OPERATOR
          && expr->econtent->cons_exp_node.Unary_operator.kind
              ->tag_uokind == UOCASTDEREF) {
        expression res = expr->econtent->cons_exp_node.Unary_operator.sub;
        free_uokind(expr->econtent->cons_exp_node.Unary_operator.kind);
        free(expr->econtent);
        free(expr);
        expr = res;
      };
      if (expr->econtent->tag_exp_node == ASSIGN) {
        expression lvalue = expr->econtent->cons_exp_node.Assign.lvalue;
        expression temp_init = expression_cons(copy_loc(lvalue->eloc),
          exp_node_Address(expression_cons(copy_loc(lvalue->eloc),
           lvalue->econtent)));
        lvalue->econtent =
          exp_node_Temporary(
            mk_tmp_name(),
            makeDefaultType(
              _clangUtils->getSourceLocation(expr->eloc),type),
            init_expr_Single_init(temp_init), false);
        expr=expression_cons(copy_loc(expr->eloc), exp_node_Dereference(expr));
      };
      return expr;
    }
  /*! 
    translates an expression. If receiver is not NULL, side-effects will
    be appended at the end of the statement list. */
  exp_node makeExpression(const clang::Expr* expr, bool* shouldDelay,
                          list* receiver=NULL);
  compilation_constant makeConstantExpression(const clang::Expr* expr) const;
  void readStatementCommentUntil(clang::SourceLocation sourceLocation,
      location& commentLocation, list& /*<statement>*/stmts,
      ForwardReferenceList& forwardStmts, const clang::Stmt* nextStmt,
      ForwardReferenceList* container, const clang::DeclContext* context);

  void makeCleanupsStmts(ForwardReferenceList& forwardStmts,
      /* stmt */ list* cursor, expression expr,
      const clang::DeclContext* context, bool* shouldDelay);
  void makeCleanupsStmts(ForwardReferenceList& forwardStmts,
      /* stmt */ list* cursor, init_expr iexpr,
      const clang::DeclContext* context, bool* shouldDelay);
  void makeCleanupsStmts(ForwardReferenceList& forwardStmts,
      /* stmt */ list* cursor, /* expression */ list exprs,
      const clang::DeclContext* context, bool* shouldDelay);
  statement makeExprWithCleanupsStmt(const clang::ExprWithCleanups* cleanups,
      location l,list& /*<statement>*/stmts, ForwardReferenceList& forwardStmts,
      const clang::DeclContext* context, bool* shouldDelay);
  statement makeCompoundStmt(const clang::CompoundStmt* block,
      location l, location commentLocation, list& /*<statement>*/stmts,
      ForwardReferenceList* container, ForwardReferenceList& forwardStmts,
      const clang::DeclContext* context, bool* shouldDelay);
  statement makeReturnStmt(const clang::ReturnStmt* returnStmt,
      location l, location commentLocation, list& /*<statement>*/stmts,
      ForwardReferenceList& forwardStmts, const clang::DeclContext* context,
      bool* shouldDelay);
  statement makeDeclStmt(const clang::DeclStmt* declStmt,
      location l, location commentLocation, list& /*<statement>*/stmts,
      ForwardReferenceList* container, ForwardReferenceList& forwardStmts,
      const clang::DeclContext* context, bool* shouldDelay);
  statement makeDoStmt(const clang::DoStmt* doStmt, location l,
      location commentLocation, list& /*<statement>*/stmts,
      ForwardReferenceList& forwardStmts, const clang::DeclContext* context,
      bool* shouldDelay);
  statement makeForStmt(const clang::ForStmt* forStmt, location l,
      location commentLocation, list& /*<statement>*/stmts,
      ForwardReferenceList& forwardStmts, const clang::DeclContext* context,
      bool* shouldDelay);
  statement makeLabelStmt(const clang::LabelStmt* labelStmt,
      location l, location commentLocation, list& /*<statement>*/stmts,
      ForwardReferenceList* container, ForwardReferenceList& forwardStmts,
      const clang::DeclContext* context, bool* shouldDelay);
  statement makeIfStmt(const clang::IfStmt* ifStmt, location l,
      location commentLocation, list& /*<statement>*/stmts,
      ForwardReferenceList& forwardStmts, const clang::DeclContext* context,
      bool* shouldDelay);
  statement makeSwitchStmt(const clang::SwitchStmt* switchStmt, location l,
      location commentLocation, list& /*<statement>*/stmts,
      ForwardReferenceList& forwardStmts, const clang::DeclContext* context,
      bool* shouldDelay);
  statement makeWhileStmt(const clang::WhileStmt* whileStmt, location l,
      location commentLocation, list& /*<statement>*/stmts,
      ForwardReferenceList& forwardStmts, const clang::DeclContext* context,
      bool* shouldDelay);
  catch_block makeCatchBlock(const clang::CXXCatchStmt* catchStmt,
      location l, location commentLocation, const clang::DeclContext* context,
      bool* shouldDelay);
  statement makeTryStmt(const clang::CXXTryStmt* tryStmt, location l,
      location commentLocation, list& /*<statement>*/stmts,
      ForwardReferenceList* container, ForwardReferenceList& forwardStmts,
      const clang::DeclContext* context, bool* shouldDelay);
  statement makeGCCAsmStmt(const clang::GCCAsmStmt* asmStmt);
  statement makeStmt(const clang::Stmt* stmt,
      ForwardReferenceList* container, const clang::DeclContext* context,
      bool* shouldDelay=NULL);
  list /*<statement>*/ makeCodeBlock(const clang::Stmt* body,
      const clang::DeclContext* context, const clang::FunctionDecl* decl,
      bool* shouldDelay=NULL);
  friend class ExpressionGuard;
  void insertNamedDeclaration(const clang::Decl* decl, bool isBefore=false);
  qual_type makeDefaultType(
    clang::SourceLocation const& loc, clang::QualType const& type);
  qual_type makeDefaultNameType(
    clang::SourceLocation const& loc, clang::QualType const& type);
  qual_type makeDefaultExternalNameType(
    clang::SourceLocation const& loc, clang::QualType const& type);

  int findCommentAfterRange(clang::SourceRange range);
  void advanceCommentUntil(clang::SourceLocation sourceLocation);

  void addLocalVariablesInSema(const clang::DeclStmt * declStmt,
      clang::Scope* scope);
  void addLocalVariablesInSema(const clang::CompoundStmt * block,
      clang::Scope* scope);
  void addLabelsInSema(const clang::CompoundStmt* block);

  clang::DiagnosticsEngine& getDiagnosticEngine() const
    { return _parents.getDiagnosticEngine(); }
  void parseGlobalComment(AnnotationComment& comment,
      const clang::DeclContext* clangContext);
  void parseCodeAnnotation(AnnotationComment& comment,
      const clang::DeclContext* clangContext,
      ForwardReferenceList* container);
  void parseLoopAnnotation(AnnotationComment& comment,
      const clang::Stmt* stmt, const clang::DeclContext* clangContext,
      ForwardReferenceList* container);
  void parseStatementAnnotation(AnnotationComment& comment,
      const clang::Stmt* stmt, const clang::DeclContext* clangContext,
      ForwardReferenceList* container);
  void parseDefaultComment(AnnotationComment& comment);
  void parseFunctionContractComment(AnnotationComment& comment, option&
      /* function_contract */ contract, const clang::FunctionDecl* decl);

  void registerTemplateDecl(clang::Decl* Decl);
  void registerAttachedNextTemplateDecl(clang::Decl* Decl);
  void readFunctionComments(clang::FunctionDecl* Decl, int& nextPreviousComment,
      bool& isNewTemplate,
      std::list<AnnotationComment*>*& templatedNextAnnotations);
  void readContractComments(clang::FunctionDecl* Decl,
      option /* function_contract */& contract, bool hasPushedBody,
      bool& hasParseTemplate, int& nextPreviousComment,
      std::list<AnnotationComment*>* templatedNextAnnotations);
  void readRecordComments(clang::RecordDecl* Decl,
      const clang::CXXRecordDecl *RD,
      const clang::ClassTemplateSpecializationDecl* TSD,
      bool& isDeportedInstantiation);
  void readInnerRecordComments(clang::RecordDecl* Decl);
  void readGlobalComment(clang::Decl* Decl, bool mayHaveTemplate);
  void readGlobalCommentUntil(
    clang::SourceLocation loc, 
    clang::DeclContext* context, bool mayHaveTemplate);
  void insertConstructorPreambleIn(const clang::CXXConstructorDecl& constructor,
      list& /*statement */ bodyref, bool* shouldDelayInit,
      ForwardReferenceList* /*statement */ bodyBare=NULL);
  void insertDestructorPreambleIn(const clang::CXXDestructorDecl& destructor,
      option /*statement list */ bodyref,
      ForwardReferenceList* /*statement */ bodyBare=NULL);
  void addDelayedImplementation(translation_unit_decl delayedFunc,
      clang::FunctionDecl* Decl, const char* name,
      option /*statement*/& delayedBody,
      /* statement list */ option bodyBare=NULL);

  access_kind get_access_kind(clang::AccessSpecifier acc) {
    switch (acc) {
      case clang::AS_public: return PUBLIC;
      case clang::AS_protected: return PROTECTED;
      case clang::AS_private: return PRIVATE;
      case clang::AS_none: {
        std::cerr << "access specifier cannot be none" << std::endl;
        exit(2);
      }
      default: {
        std::cerr << "unknown access specifier" << std::endl;
        exit(2);
      }
    }
  }

  /* inheritance */ list makeInheritanceList(clang::CXXRecordDecl* cxxDecl,
      std::vector<const clang::Decl*>* unvisitedInstanceDecls,
      std::vector<const clang::CXXRecordDecl*>* unvisitedBases);
  void ensureBuiltinDeclaration(unsigned builtinID,
      const clang::FunctionDecl* fd, bool doesForceVariadic=false);
  void ensureVaListDeclaration(const clang::RecordDecl* decl);
  friend class ImmediateGlobalDependency;

public:
  FramacVisitor(FILE* outstream, clang::CompilerInstance& compilerInstance);

  void setAnnotError() { _clangUtils->setAnnotError(); }
  void setGenerateImplicitMethods()
    { _clangUtils->setGenerateImplicitMethods(); }
  void setGenerateBareFunctions()
    { _clangUtils->setGenerateBareFunctions(); }
  void setVerbose() { _clangUtils->setVerbose(); }
  ~FramacVisitor() override
    { free(_clangUtils);
      free(_intermediateAST);
      if (_implicitThisStar) free_expression(_implicitThisStar);
    }

    void parseGhostStatement(
      AnnotationComment& comment,
      const clang::DeclContext* clangContext,
      ForwardReferenceList* container);
    void parseGhostGlobal(
      AnnotationComment& comment,
      clang::DeclContext* clangContext);

  bool HandleTopLevelDecl(clang::DeclGroupRef Decls) override;

  void HandleTranslationUnit(clang::ASTContext &context) override;
  void handleLexicalPostVisit(const clang::DeclContext* currentContext);
  void handleSemanticPostVisit(const clang::DeclContext* currentContext);
  void handlePostVisit(const clang::DeclContext* lexicalCurrentContext,
      const clang::DeclContext* semanticCurrentContext)
    { // Since the whole lexical part is handled before the whole semantic part.
      // TODO. a step by step approach for both
      //       maybe with Traverse...Decl that would do it automatically
      //       for the common upper part of both stacks (lexical and semantic).
      State semanticState = _state;
      handleLexicalPostVisit(lexicalCurrentContext);
      State lexicalState = _state;
      _state = semanticState;
      handleSemanticPostVisit(semanticCurrentContext);
      if (_state != lexicalState) {
        if (lexicalState & SInstanceSynchronized)
          _state = (State) (_state | SInstanceSynchronized);
        else
          _state = (State) (_state & ~SInstanceSynchronized);
      }
    }

  virtual bool VisitNamedDecl(clang::NamedDecl *Decl)
    { // handlePostVisit(Decl->getDeclContext());
      return true;
    }
  virtual bool VisitFunctionDecl(clang::FunctionDecl* Decl);
  virtual bool shouldVisitTemplateInstantiations() const { return true; }
  virtual bool shouldVisitImplicitCode() const { return true; }
  virtual bool VisitNamespaceDecl(clang::NamespaceDecl* Decl);
  virtual bool TraverseNamespaceDecl(clang::NamespaceDecl* Decl);
  virtual bool TraverseLinkageSpecDecl(clang::LinkageSpecDecl* Decl);
  virtual bool TraverseLambdaExpr(clang::LambdaExpr* e) {
    // treatment of LambdaExpr is done entirely at the current node;
    // traversing children can only confuse the translator.
    return true;
  }
  bool localLexicalVisitNamespaceDecl(clang::NamespaceDecl* Decl);
  bool localSemanticVisitNamespaceDecl(clang::NamespaceDecl* Decl);
  virtual bool VisitEnumDecl(clang::EnumDecl* Decl);
  virtual bool VisitRecordDecl(clang::RecordDecl* Decl);
  virtual bool VisitClassTemplatePartialSpecializationDecl(
      clang::CXXRecordDecl* Decl);
  virtual bool TraverseFriendDecl(clang::FriendDecl* Decl)
    { handlePostVisit(Decl->getLexicalDeclContext(), Decl->getDeclContext());
      _tableForWaitingDeclarations.addDeclaration(Decl->getFriendDecl(),
          _globals);
      return true;
    }
  virtual bool TraverseFriendTemplateDecl(clang::FriendTemplateDecl* Decl)
    { handlePostVisit(Decl->getLexicalDeclContext(), Decl->getDeclContext());
      return true;
    }
  bool localLexicalVisitRecordDecl(clang::RecordDecl* Decl);
  bool localSemanticVisitRecordDecl(clang::RecordDecl* Decl);
  virtual bool VisitTypedefNameDecl(clang::TypedefNameDecl* Decl);
  virtual bool VisitFieldDecl(clang::FieldDecl* Decl);
  virtual bool VisitVarDecl(clang::VarDecl* Decl);
  void postLexicalVisitRecordDecl(clang::RecordDecl* Decl,
      int& templateContextsNumber);
  void postSemanticVisitRecordDecl(clang::RecordDecl* Decl);
  void postLexicalVisitNamespaceDecl(clang::NamespaceDecl* Decl);
  void postSemanticVisitNamespaceDecl(clang::NamespaceDecl* Decl);
  void postHandleTranslationUnit();
  void outputIntermediateFormat () const
    { std::cout << "Now output intermediate result\n";
      output_file(_outFile, _intermediateAST);
      fflush(_outFile);
    }

  expression makeLocExpression(const clang::Expr* expr,
      bool* shouldDelay=NULL, list* receiver=NULL);
};

class FramaCIRGenAction::UnvisitedNameRegistration
  : public Clang_utils::VirtualDeclRegistration {
private:
  typedef Clang_utils::VirtualDeclRegistration inherited;
  FramacVisitor& _visitor;
  bool _isExternal;

public:
  UnvisitedNameRegistration(FramacVisitor& visitor)
    : _visitor(visitor), _isExternal(false) { setRegisterDecl(); }
  UnvisitedNameRegistration(const UnvisitedNameRegistration& source)
    : inherited(source), _visitor(source._visitor),
      _isExternal(source._isExternal) {}

  void registerDecl(const clang::Decl* decl) override
    { if (!_visitor._tableForWaitingDeclarations.hasVisited(decl)) {
        InstanceContexts::UnvisitedDecls::const_iterator
          iterEnd = _visitor.unvisitedNameDecls().end();
        bool hasFound = false;
        for (InstanceContexts::UnvisitedDecls::const_iterator
            iter = _visitor.unvisitedNameDecls().begin();
            !hasFound && iter != iterEnd; ++iter)
          hasFound = (*iter == decl);
        if (!hasFound)
          _visitor.unvisitedNameDecls().push_back(decl);
      }
      else if (!_isExternal && decl->getDeclContext()->isRecord()) {
        assert(llvm::dyn_cast<clang::RecordDecl>(decl->getDeclContext()));
        // typedefs are not instantiated if they don't depend
        //   of the template arguments
        bool doesAvoidTemplateClass = false;
        const clang::CXXRecordDecl *RD = llvm::dyn_cast<clang::CXXRecordDecl>
            (decl->getDeclContext());
        if (RD && RD->getDescribedClassTemplate()
            && (RD->getDescribedClassTemplate()->getTemplatedDecl() == RD))
          doesAvoidTemplateClass = true;
        else if (RD && (RD->getKind()
            == clang::Decl::ClassTemplatePartialSpecialization))
          doesAvoidTemplateClass = true;
        if (!doesAvoidTemplateClass)
          _visitor._tableForWaitingDeclarations.ensureGeneration(
            static_cast<const clang::RecordDecl*>(decl->getDeclContext()),
            _visitor.unvisitedDecls());
      };
    }
  void setExternal() { _isExternal = true; }
  FramacVisitor& getVisitor() const { return _visitor; }
};

class FramaCIRGenAction::UnvisitedRegistration
    : public Clang_utils::VirtualDeclRegistration {
private:
  typedef Clang_utils::VirtualDeclRegistration inherited;
  UnvisitedNameRegistration _unvisitedName;

public:
  UnvisitedRegistration(FramacVisitor& visitor) : _unvisitedName(visitor)
    { setRegisterDecl(); _unvisitedName.setExternal(); }
  UnvisitedRegistration(const UnvisitedRegistration& source)
    : inherited(source), _unvisitedName(source._unvisitedName) {}

  void registerDecl(const clang::Decl* decl) override
    { std::vector<const clang::Decl*> alternativeDecls;
      if (!_unvisitedName.getVisitor()._tableForWaitingDeclarations
          .hasVisited(decl, &alternativeDecls)) {
        if (!alternativeDecls.empty()) {
          decl = alternativeDecls.back();
          alternativeDecls.pop_back();
        };
        while (decl) {
          typedef std::vector<const clang::Decl*> UnvisitedDecls;
          bool hasFound = false;
          UnvisitedDecls::const_iterator
            iterEnd = _unvisitedName.getVisitor().unvisitedDecls().end(),
            iter = _unvisitedName.getVisitor().unvisitedDecls().begin();
          for (; !hasFound && iter != iterEnd; ++iter)
            hasFound = (*iter == decl);
          if (!hasFound)
            _unvisitedName.getVisitor().unvisitedDecls().push_back(decl);
          if (!alternativeDecls.empty()) {
            decl = alternativeDecls.back();
            alternativeDecls.pop_back();
          }
          else
            decl = NULL;
        };
      }
    }
  VirtualDeclRegistration* getNameRegistration() override
    { return &_unvisitedName; }
};

class FramaCIRGenAction::VerifyNameRegistration
  : public Clang_utils::VirtualDeclRegistration {
private:
  typedef Clang_utils::VirtualDeclRegistration inherited;
  FramacVisitor& _visitor;

public:
  VerifyNameRegistration(FramacVisitor& visitor) : _visitor(visitor)
    { setRegisterDecl(); }
  VerifyNameRegistration(const VerifyNameRegistration& source)
    : inherited(source), _visitor(source._visitor) {}

  void registerDecl(const clang::Decl* decl) override
    { if (!_visitor._tableForWaitingDeclarations.hasVisited(decl)) {
        clang::Decl::Kind kindDecl = decl->getKind();
        if ((kindDecl >= clang::Decl::firstRecord
              && kindDecl <= clang::Decl::lastRecord)
            || (kindDecl == clang::Decl::Typedef))
          _visitor.insertNamedDeclaration(decl, true /* isBefore */);
        if (kindDecl == clang::Decl::Typedef) {
          _visitor._tableForWaitingDeclarations.addDeclaration(decl,
              _visitor._globals);
          // _visitor._instanceContexts.removeUnvisited(Decl);
        };
      };
    }
  FramacVisitor& getVisitor() const { return _visitor; }
};

class FramaCIRGenAction::ExpressionGuard {
private:
  const FramacVisitor& _visitor;
  expression _thisStarExpr;

public:
  ExpressionGuard(const FramacVisitor& visitor, expression& thisStarExpr)
    : _visitor(visitor), _thisStarExpr(thisStarExpr)
    { thisStarExpr = NULL; }
  ~ExpressionGuard() { if (_thisStarExpr) free_expression(_thisStarExpr); }

  exp_node setAssignResult(exp_node result, const clang::Expr* expr)
    { if (_thisStarExpr) {
        location loc = _visitor.makeLocation(expr->getSourceRange());
        result = exp_node_Assign(_thisStarExpr, expression_cons(loc,result));
        expression_cons(loc, result);
        _thisStarExpr = NULL;
      }
      return result;
    }

  exp_node setAssignResult(expression result, const clang::Expr* expr) {
    exp_node res = setAssignResult(result->econtent, expr);
    result->econtent = NULL;
    free_expression(result);
    return res;
  }

  expression releaseExpr()
    { expression result = _thisStarExpr; 
      if (!result) {
        std::cerr << "Need a this context!" << "\nAborting\n";
        exit(2);
      };
      _thisStarExpr = NULL;
      return result;
    }
};

#endif // CLANG_VisitorH

