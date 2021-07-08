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

#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/APValue.h"
#include "clang/Basic/FileManager.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/CompilerInvocation.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/Utils.h"
#include "clang/Sema/Scope.h"
#include "Clang_utils.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Host.h"
#include "llvm/ADT/ArrayRef.h"
#include <iostream>
#include <fstream>
#include <sstream>
#include <cstddef>
#include <list>
#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic pop
#endif

#include "ClangVisitor.h"

void
AnnotationCommentList::add(AnnotationComment* comment,
    clang::SourceManager &sourceManager) {
  if (!comment || !comment->isValid())
    return;

  // Check if the comments are not in source order.
  while (!empty()
      && !sourceManager.isBeforeInTranslationUnit(
          back()->getSourceRange().getBegin(),
          comment->getSourceRange().getBegin())) {
    // If they are, just pop a few last comments that don't fit.
    // This happens if an \#include directive contains comments.
    back()->freeContent();
    delete back();
    pop_back();
  }
  push_back(comment);
}

std::unique_ptr<clang::ASTConsumer>
FramaCIRGenAction::CreateASTConsumer(clang::CompilerInstance& CI,
    clang::StringRef InFile)
{ FramacVisitor* vis = new FramacVisitor(_outFile, _compilerInstance);
  if (_annotError) vis->setAnnotError();
  if (_doesGenerateImplicitMethods) vis->setGenerateImplicitMethods();
  if (_isVerbose) vis->setVerbose();
  return std::unique_ptr<clang::ASTConsumer>(vis);
}

/**************************************************************/
/* Implementation of the class FramaCIRGenAction::DeclContext */
/**************************************************************/

void
FramaCIRGenAction::DeclContext::reopenLexicalHierarchy(
    FramacVisitor& visitor) {
  std::list<LexicalLocalDeclContext>::iterator
    iter = _lexicalParent.begin(),
    iterEnd = _lexicalParent.end();
  if (iter != iterEnd) {
    assert(iter->isNamespace());
    assert(llvm::dyn_cast<const clang::NamespaceDecl>(iter->getSynchro()));
    const clang::NamespaceDecl* namespaceDecl
      = static_cast<const clang::NamespaceDecl*>(iter->getSynchro());
    char* name=const_cast<char*>(copy_string(namespaceDecl->getName().str()));
    location loc = visitor.makeDeclLocation(*namespaceDecl);
    translation_unit_decl decl
      = translation_unit_decl_Namespace(loc, name, NULL);
    visitor._globals.insertContainer(decl);
    /* translation_unit_decl */ list* namespaceElements
      = &decl->cons_translation_unit_decl.Namespace.body;
    iter->resetNamespace(*namespaceElements, iter->getSynchro());
    LexicalLocalDeclContext* previous = &*iter;
    for (++iter; iter != iterEnd; ++iter) {
      assert(iter->isNamespace());
      assert(llvm::dyn_cast<const clang::NamespaceDecl>(iter->getSynchro()));
      const clang::NamespaceDecl* namespaceDecl
        = static_cast<const clang::NamespaceDecl*>(iter->getSynchro());
      char* name=const_cast<char*>(copy_string(namespaceDecl->getName().str()));
      location loc = visitor.makeLocation(namespaceDecl->getSourceRange());
      translation_unit_decl decl
        = translation_unit_decl_Namespace(loc, name, NULL);
      assert(!*namespaceElements);
      *namespaceElements = cons_container(decl, NULL);
      previous->getDeclarations().advanceToEnd();
      namespaceElements = &decl->cons_translation_unit_decl.Namespace.body;
      iter->resetNamespace(*namespaceElements, iter->getSynchro());
      previous = &*iter;
    };
  };
}

void
FramaCIRGenAction::DeclContext::pushFunctionBody(
    clang::FunctionDecl* functionDecl)
{ // see Sema::ActOnStartOfFunctionDef
  clang::Scope* scope = new clang::Scope(_scope,
    clang::Scope::FnScope | clang::Scope::DeclScope, _diags);
  _scope = scope;
  _sema->PushFunctionScope();
  // _sema->PushDeclContext(scope, functionDecl);
  _sema->EnterDeclaratorContext(scope, functionDecl);
  scope->AddDecl(functionDecl);
  for (unsigned p=0, NumParams = functionDecl->getNumParams();
      p < NumParams; ++p) {
    clang::ParmVarDecl *Param = functionDecl->getParamDecl(p);
    // If this has an identifier, add it to the scope stack.
    if (Param->getIdentifier())
      // scope->AddDecl(Param);
      _sema->PushOnScopeChains(Param, _scope, false);
  }
  pushCompoundScope();
  _currentFunctionBody = functionDecl;
}

void
FramaCIRGenAction::DeclContext::popFunctionBody(
    clang::FunctionDecl* functionDecl)
{ clang::Scope* scope = _scope->getParent();
  _sema->PopCompoundScope();
  _sema->ExitDeclaratorContext(_scope);
  assert(scope);
  delete _scope;
  _scope = scope;
  // _sema->PopDeclContext();
  _sema->PopFunctionScopeInfo(NULL, functionDecl);
  _currentFunctionBody = NULL;
}

void
FramaCIRGenAction::DeclContext::setLocalPush(
    const clang::DeclContext* parentDecl) {
  std::list<const clang::DeclContext*> reverseDecl;
  assert(!_semanticParent.empty());
  while (parentDecl && parentDecl != _semanticParent.back().getSynchro()) {
    reverseDecl.push_back(parentDecl);
    parentDecl = parentDecl->getParent();
  };
  assert(parentDecl && _localPush == 0);
  std::list<const clang::DeclContext*>::const_reverse_iterator
    iterEnd = reverseDecl.rend();
  for (std::list<const clang::DeclContext*>::const_reverse_iterator
      iter = reverseDecl.rbegin(); iter != iterEnd; ++iter) {
    _semanticParent.push_back(_semanticParent.back().findDecl(*iter));
    clang::Scope* scope = new clang::Scope(_scope, 0, _diags);
    _scope = scope;
    _sema->EnterDeclaratorContext(_scope,
        const_cast<clang::DeclContext*>(_semanticParent.back().getSynchro()));
    ++_localPush;
  };
}

/*
void
FramaCIRGenAction::DeclContext::setLocalPushInstantiation(
    option& declarations, const clang::DeclContext* classContext) {
  assert(_localPush == 0);
  bool hasFound = false;
  if (!_semanticParent.empty()) {
    LocalDeclContext found = _semanticParent.back().findDecl(classContext);
    if ((hasFound = found.isValid()) != false)
      _semanticParent.push_back(found);
  };
  if (!hasFound) {
    assert(classContext->isRecord());
    pushSemanticClass(declarations, classContext);
  };

  clang::Scope* scope = new clang::Scope(_scope, 0, _diags);
  _scope = scope;
  _sema->EnterDeclaratorContext(_scope,
      const_cast<clang::DeclContext*>(classContext));
  ++_localPush;
}
*/

void
FramaCIRGenAction::DeclContext::clearLocalPush() {
  while (_localPush > 0) {
    clang::Scope* scope = _scope->getParent();
    _sema->ExitDeclaratorContext(_scope);
    assert(scope);
    delete _scope;
    _scope = scope;
    _semanticParent.pop_back();
    --_localPush;
  };
}

void
FramaCIRGenAction::DeclContext::lexicalSynchronizeWith(
    const clang::DeclContext* parentDecl, FramacVisitor& visitor) {
  if (!parentDecl || !parentDecl->getLexicalParent()
      || parentDecl->getDeclKind()==clang::Decl::LinkageSpec) {
    size_t nbPops = _lexicalParent.size();
    if (nbPops > 0) {
      do {
        _lexicalParent.back().clear();
        _lexicalParent.pop_back();
      } while (--nbPops);
      assert(_lexicalParent.empty());
    };
  }
  else {
    assert(!_lexicalParent.empty());
    while (!parentDecl->Equals(_lexicalParent.back().getSynchro())) {
      _lexicalParent.back().clear();
      _lexicalParent.pop_back();
      if (_lexicalParent.empty()) {
         const clang::DeclContext* cursorDecl = parentDecl->getLexicalParent();
         while (cursorDecl->getLexicalParent()
             && (cursorDecl->getDeclKind()==clang::Decl::LinkageSpec))
           cursorDecl = cursorDecl->getLexicalParent();
         assert(!cursorDecl->getLexicalParent()
             && Clang_utils::isExternCContext(parentDecl));
         return;
      };
    };
  };
}

void
FramaCIRGenAction::DeclContext::semanticSynchronizeWith(
    const clang::DeclContext* parentDecl, FramacVisitor& visitor) {
  if (!parentDecl || !parentDecl->getParent()
      || parentDecl->getDeclKind()==clang::Decl::LinkageSpec) {
    size_t nbPops = _semanticParent.size();
    if (nbPops > 0) {
      do {
        _semanticParent.back().clear();
        _semanticParent.pop_back();
        clang::Scope* scope = _scope->getParent();
        _sema->ExitDeclaratorContext(_scope);
        assert(scope);
        delete _scope;
        _scope = scope;
        // _sema->PopDeclContext();
      } while (--nbPops);
      assert(_semanticParent.empty());
    };
  }
  else {
    assert(!_semanticParent.empty());
    while (!parentDecl->Equals(_semanticParent.back().getSynchro())) {
      clang::Scope* scope = _scope->getParent();
      _sema->ExitDeclaratorContext(_scope);
      assert(scope);
      delete _scope;
      _scope = scope;
      _semanticParent.back().clear();
      _semanticParent.pop_back();
      if (_semanticParent.empty()) {
         const clang::DeclContext* cursorDecl = parentDecl->getParent();
         while (cursorDecl->getParent()
             && (cursorDecl->getDeclKind()==clang::Decl::LinkageSpec))
           cursorDecl = cursorDecl->getParent();
         assert(!cursorDecl->getParent()
             && Clang_utils::isExternCContext(parentDecl));
         return;
      };
    };
  };
}

void
FramaCIRGenAction::DeclContext::clearLexical(FramacVisitor& visitor) {
  size_t nbPops = _lexicalParent.size();
  if (nbPops > 0) {
    do {
      _lexicalParent.back().clear();
      _lexicalParent.pop_back();
    } while (--nbPops);
    assert(_lexicalParent.empty());
  };
}

void
FramaCIRGenAction::DeclContext::clearSemantic(FramacVisitor& visitor) {
  size_t nbPops = _semanticParent.size();
  if (nbPops > 0) {
    do {
      _semanticParent.back().clear();
      _semanticParent.pop_back();
      clang::Scope* scope = _scope->getParent();
      _sema->ExitDeclaratorContext(_scope);
      assert(scope);
      delete _scope;
      _scope = scope;
      // _sema->PopDeclContext();
    } while (--nbPops);
    assert(_semanticParent.empty());
  };
}

/********************************************************/
/* Implementation of the class AnnotationCommentHandler */
/********************************************************/

bool
FramaCIRGenAction::AnnotationCommentHandler::HandleComment(
    clang::Preprocessor &PP, clang::SourceRange commentRange) {
  if (!_sourceManager)
    _sourceManager = &_compilerInstance.getSourceManager();
  if (!_sema) _sema = &_compilerInstance.getSema();

  AnnotationComment* comment = AnnotationCommentFactory
    ::createAnnotationComment(*_sourceManager, commentRange, _sema);
  if (!comment || !comment->isValid()) {
    if (comment) {
      comment->freeContent();
      delete comment;
    };
    return false;
  };
  _visitor._annotationCommentList.add(comment, *_sourceManager);
  return false;
}

/***************************************/
/* Implementation of the class Visitor */
/***************************************/

FramacVisitor::FramacVisitor(
  FILE* outstream, clang::CompilerInstance& compilerInstance)
  : _outFile(NULL), _sema(NULL), 
    _parents(compilerInstance.getDiagnostics()), _state(SSynchronized),
    _context(NULL), _implicitThisStar(NULL),
    _isImplicitThisBare(false),
    _ghost(false), _ghost_set(),
    _commentHandler(compilerInstance, *this), _commentIndex(-1),
    _templateCommentIndex(-2), _lexicalContextForPostVisit(NULL),
    _semanticContextForPostVisit(NULL),
    _typeFunctionResult(NULL),
    _generatedVaList(false),
    _templateContextsNumber(0)
{ _outFile = outstream;
  _clangUtils = new Clang_utils(NULL, this);
  _intermediateAST = (file)malloc(sizeof(*_intermediateAST));
  _intermediateAST->globals=NULL;
  _commentHandler.compilerInstance().getPreprocessor()
      .addCommentHandler(&_commentHandler);
  _globals = ForwardDoubleReferenceList(_intermediateAST->globals);
  _tableForWaitingDeclarations.setUtils(_clangUtils);
  struct _location loc = {"", 0, 0, "", 0, 0};
  _rttiTable.insertVMTAndRttiPrelude(_globals, &loc);
  memset(_generatedBuiltins, 0, SizeOfBuiltinArray*sizeof(unsigned));
}

void
FramacVisitor::HandleTranslationUnit(clang::ASTContext &context)
{ int numberOfErrors = _commentHandler.compilerInstance().getDiagnostics()
      .getClient()->getNumErrors();
  if (numberOfErrors > 0) {
    if (numberOfErrors == 1)
      std::cerr << "code generation aborted due to one compilation error";
    else
      std::cerr << "code generation aborted due to compilation errors";
    std::cerr << std::endl;
    exit(2);
  };
  _context = &context;
  _clangUtils->set_context(&context);
  _sema = &_commentHandler.compilerInstance().getSema();
  _parents.setTranlationUnit(context, *_sema);
  _state = SSynchronized;
  clang::SourceManager& sources = context.getSourceManager();
  auto fname = sources.getFileEntryForID(sources.getMainFileID())->getName();
  _intermediateAST->filename = fname.str().c_str();
  _lexicalContextForPostVisit = context.getTranslationUnitDecl();
  _semanticContextForPostVisit = context.getTranslationUnitDecl();
  TraverseDecl(context.getTranslationUnitDecl());
  handlePostVisit(context.getTranslationUnitDecl(),
    context.getTranslationUnitDecl());
  postHandleTranslationUnit();
  _lexicalContextForPostVisit = NULL;
  _semanticContextForPostVisit = NULL;
  bool haveWaitingDeclarationsBeenGenerated
    = _tableForWaitingDeclarations.isComplete();
  if (!_alternateInstanceContexts.empty()) {
     std::cerr << "Internal error in the visit of RecordDecl "
        "and friend declarations\n";
#if 1
     assert(false);
#endif
  };
  if (!haveWaitingDeclarationsBeenGenerated
      || _delayedImplementations.getFront()
      || !_immediateGlobalDependency.isEmpty()) {
    assert(_immediateGlobalDependency.isEmpty());
    if (!haveWaitingDeclarationsBeenGenerated) {
      std::cerr << "The following declarations have not been generated:\n";
      _tableForWaitingDeclarations.printIncompleteDeclarations(std::cerr);
    }
    else if (_delayedImplementations.getFront()) {
      auto current =
        ((translation_unit_decl)(*_delayedImplementations.getFront())
         .element.container)
        ->cons_translation_unit_decl.Function.fun_name
        ->cons_decl_or_impl_name.Implementation.name;
      std::cerr << "Assertion broken in:" <<
        current->decl_name << std::endl;
      std::cerr << "\n" ;
    }
#if 1
    assert(!haveWaitingDeclarationsBeenGenerated
      ? (bool) _delayedImplementations.getFront()
      : !_delayedImplementations.getFront());
#endif
  };
  assert(!_rttiTable.hasDelayedMethodCalls());
  assert(!_clangUtils->hasTemplateInstance());
  outputIntermediateFormat();
}

// [TODO] see the implementation of
//   RawComment *ASTContext::getRawCommentForDeclNoCache(const Decl *D) const
//   for the header of ::Visitor::Visit... methods handling with comments.

// [TODO] see the implementation of
//   const RawComment *ASTContext::getRawCommentForAnyRedecl(
//       const Decl *D, const Decl **OriginalDecl) const
//   for the header of ::Visitor::Visit... methods handling with comments.

init_expr
FramacVisitor::makeInitExpr(
  const clang::QualType & typ, const clang::Expr* init, bool* shouldDelay) {
  if (init->getStmtClass() == clang::Stmt::ExprWithCleanupsClass) {
    const auto expr = llvm::dyn_cast<const clang::ExprWithCleanups>(init);
    // it might mask an InitListExpr. ExprWithCleanups does not have
    // reference to destructors to call at the end of the block (and more
    // importantly when to call them) and Frama-C 15 Silicium will be equipped
    // to deal with them anyways: nothing is really needed on the C++ side
    // of the plugin.
    return makeInitExpr(typ, expr->getSubExpr(), shouldDelay);
  }
  if (init->getStmtClass() == clang::Stmt::InitListExprClass) {
    assert (llvm::dyn_cast<const clang::InitListExpr>(init));
    clang::InitListExpr const *init_list
        = static_cast<const clang::InitListExpr*>(init);
    // Use the semantic form, where compound initialization is done
    // in appropriate order.
    if (!init_list->isSemanticForm() && init_list->getSemanticForm()) {
      init_list = init_list->getSemanticForm();
    }
    const clang::FieldDecl* union_field
      = init_list->getInitializedFieldInUnion();
    if (union_field) {
      const char* field_name = copy_string(union_field->getNameAsString());
      clang::QualType ctype = union_field->getType();
      qual_type field_type = makeDefaultType(union_field->getLocation(), ctype);
      clang::InitListExpr::const_iterator field_init = init_list->begin();
      clang::InitListExpr::const_iterator field_end = init_list->end();
      if (field_init+1 != field_end) {
        std::cerr << "More than one initializer for an union.\n";
#if CLANG_VERSION_MAJOR >= 11
        init->dump(llvm::errs(), *_context);
#else
        init->dump(llvm::errs(), _context->getSourceManager());
#endif
        std::cerr << "Aborting\n";
        exit(2);
      };
      init_expr definition = makeInitExpr(
          ctype, static_cast<clang::Expr const *>(*field_init), shouldDelay);
      return init_expr_Union_init(field_name,field_type,definition);
    }
    clang::InitListExpr::const_reverse_iterator current = init_list->rbegin();
    clang::InitListExpr::const_reverse_iterator end = init_list->rend();
    list /* init_expr */ inits = NULL;
    if (_implicitThisStar) {
      free_expression(_implicitThisStar);
      _implicitThisStar = NULL; // Compound initialization is a C thing
      _isImplicitThisBare = false;
    };
    while(current != end) {
      auto subinit = static_cast<const clang::Expr*>(*current);
      init_expr curr_init =
        makeInitExpr(subinit->getType(), subinit, shouldDelay);
      inits = cons_container(curr_init,inits);
      current++;
    }
    return init_expr_Compound_init(inits);
  };
  if (typ->isConstantArrayType() &&
      init->getStmtClass() == clang::Stmt::CXXConstructExprClass) {
    // array of objects initialized with default constructor.
    assert(_implicitThisStar);
    qualified_name idx = qualified_name_cons(NULL, "__fc_idx");
    _implicitThisStar =
      expression_cons(
        copy_loc(_implicitThisStar->eloc),
        exp_node_ArrayAccess(
          _implicitThisStar,
          expression_cons(
            copy_loc(_implicitThisStar->eloc),
            exp_node_Variable(variable_Local(idx)))));
    return
      init_expr_Array_init(
        qualified_name_dup(idx), makeLocExpression(init,shouldDelay));
  };
  if (clang::ImplicitValueInitExpr::classof(init)) {
    return init_expr_Implicit_init();
  }
  //TODO: there are other initializer classes.
  //Need to check whether they are used in the elaborated AST.
  // plain expression
   return init_expr_Single_init(makeLocExpression(init, shouldDelay));
}

init_expr FramacVisitor::make_explicit_initializer_list(const clang::Expr* e) {
  // It's likely that we'll always end up with a MaterializeTemporaryExpr,
  // but there might be cases where clang give the list directly in e.
  if (e->getStmtClass() == clang::Stmt::MaterializeTemporaryExprClass) {
    auto tmp = llvm::dyn_cast<const clang::MaterializeTemporaryExpr>(e);
#if CLANG_VERSION_MAJOR >= 10
    e = tmp->getSubExpr();
#else
    e = tmp->GetTemporaryExpr();
#endif
  }
  assert("Expecting an InitListExpr under a CXXStdInitializeListExpr"
         && e->getStmtClass() == clang::Stmt::InitListExprClass);
  auto list = llvm::dyn_cast<const clang::InitListExpr>(e);
  return makeInitExpr(list->getType(), list);
}

exp_node FramacVisitor::make_initializer_list(
  const clang::CXXStdInitializerListExpr* il) {
  const clang::QualType typ = il->getType();
  const clang::CXXRecordDecl* il_type = typ->getAsCXXRecordDecl();
  assert(il_type);
  auto il_inst =
    llvm::dyn_cast<const clang::ClassTemplateSpecializationDecl>(il_type);
  assert(il_inst);
  const clang::QualType elt_type =
    il_inst->getTemplateInstantiationArgs().get(0).getAsType();
  qual_type elt_type_trans =
    makeDefaultType(_clangUtils->getBeginLoc(*il), elt_type);
  init_expr init = make_explicit_initializer_list(il->getSubExpr());
  return exp_node_InitializerList(elt_type_trans, init);
}

exp_node FramacVisitor::make_lambda_expr(const clang::LambdaExpr* lam) {
  const clang::CXXMethodDecl* lam_meth = lam->getCallOperator();
  qual_type lam_rt =
    makeDefaultExternalNameType(
      lam_meth->getReturnTypeSourceRange().getBegin(),
      lam_meth->getReturnType());
  /* arg_decl */ list lam_args = NULL;
  auto args = lam_meth->parameters();
  for (auto it = args.rbegin(); it < args.rend(); it++) {
    std::string name = (*it)->getNameAsString();
    qual_type arg_type =
      makeDefaultExternalNameType(
        (*it)->getLocation(), (*it)->getOriginalType());
    location l = makeLocation((*it)->getSourceRange());
    lam_args =
      cons_container(arg_decl_cons(arg_type, copy_string(name), l),lam_args);
  }
  /* closure */ list lam_closure =
    _clangUtils->make_capture_list(lam->captures());
  /* statement */ list lam_body =
    makeCodeBlock(lam_meth->getBody(), lam_meth->getDeclContext(), lam_meth);
  return exp_node_LambdaExpr(lam_rt, lam_args, lam_closure, lam_body);
}

expression
FramacVisitor::makeLocExpression(
  const clang::Expr* expr, bool* shouldDelay, list* receiver) {
  exp_node node = makeExpression(expr, shouldDelay, receiver);
  location loc = makeLocation(expr->getSourceRange());
  return expression_cons(loc,node);
}

exp_node FramacVisitor::convert_result(
  FramaCIRGenAction::ExpressionGuard& guard, const clang::QualType& ret,
  exp_node call, const clang::Expr* expr) {
  exp_node result = call;
  if (ret->isReferenceType())
    result =
      exp_node_Dereference(
        expression_cons(makeLocation(expr->getSourceRange()), result));
  clang::CXXRecordDecl* class_decl = ret->getAsCXXRecordDecl();
  if (class_decl) {
    clang::CXXConstructorDecl* cons =
      _sema->LookupCopyingConstructor(
        class_decl,ret.getCVRQualifiers());
    if(!cons) {
      std::cerr << 
        "Not able to find an appropriate copy constructor for class "
                << class_decl->getNameAsString() << "\nAborting.\n";
      exit(2);
    }
    // create a temporary in case the address is taken
    // but do not use copy constructor, as clang has determined
    // that it can be elided (§12.8.32).
    const char* temp = mk_tmp_name ();
    qual_type typ =makeDefaultType(expr->getExprLoc(), ret);
    expression res =
      expression_cons(makeLocation(expr->getSourceRange()),result);
    result = exp_node_Temporary(temp,typ,init_expr_Single_init(res), false);
  }
  return guard.setAssignResult(result, expr);
}

exp_node FramacVisitor::makeTemporaryObjectExpression(
  const clang::CXXTemporaryObjectExpr* constructor,
  bool* shouldDelay, /* statement */ list* receiver)
{ clang::SourceLocation sloc = constructor->getExprLoc();
  location loc = makeLocation(constructor->getSourceRange());
  assert(llvm::dyn_cast<clang::FunctionDecl>(constructor->getConstructor()));
  const clang::FunctionDecl* function = static_cast<const clang
      ::FunctionDecl*>(constructor->getConstructor());
  tkind templateExtension = NULL;
  if (function->getTemplateSpecializationKind()
      >= clang::TSK_ImplicitInstantiation) {
    clang::FunctionTemplateSpecializationInfo* info
      = function->getTemplateSpecializationInfo();
    if (info)
      templateExtension=
        tkind_TTemplateInstance(_clangUtils->getTemplateExtension(info));
  };
  if (!templateExtension)
    templateExtension = tkind_TStandard();
  qualified_name name = _clangUtils->makeQualifiedName(*function);
  if (strlen(name->decl_name) == 0) {
    free(const_cast<char*>(name->decl_name));
    name->decl_name = strdup("constructor-special");
  };
  clang::CXXConstructExpr::const_arg_iterator argEnd = constructor->arg_end();
  list /* expression */ arguments = NULL;
  ForwardReferenceList forwardArguments(arguments);
  const char* temp = mk_tmp_name();
  // [TODO] declare tmpvar in the list of local variables ?
  expression tmpvar = expression_cons(loc, exp_node_Address(
      expression_cons(copy_loc(loc), exp_node_Variable(
        variable_Local(qualified_name_cons(NULL,temp))))));
  forwardArguments.insertContainer(tmpvar);
  for (clang::CXXConstructExpr::const_arg_iterator
      argIter = constructor->arg_begin(); argIter != argEnd; ++argIter) {
    exp_node argument = makeExpression(*argIter, shouldDelay,receiver);
    expression eargument = expression_cons(makeLocation(
          (*argIter)->getSourceRange()), argument);
    forwardArguments.insertContainer(eargument);
  };
  signature sig = _clangUtils->makeSignature(*constructor->getConstructor());
  exp_node call_node =
    exp_node_Static_call(
      name, sig, funkind_FKConstructor(true),
      arguments, templateExtension, false);
  expression call = expression_cons(copy_loc(loc),call_node);
  qual_type typ = makeDefaultType(sloc, constructor->getType());
  return exp_node_Temporary(strdup(temp), typ,
      init_expr_Single_init(call), false);
}

exp_node FramacVisitor::makeConstructExpression(
  const clang::CXXConstructExpr* constructor,
  bool* shouldDelay, /* statement */ list* receiver,
  bool hasImplicitThisStar,
  bool isImplicitThisBare,
  FramaCIRGenAction::ExpressionGuard& guard)
{ tkind templateExtension = NULL;
  if (constructor->isElidable() && constructor->getNumArgs() == 1) {
    // constructor can be omitted. Gain quite a few temporary variables
    // by doing it.
    // TODO: maybe some additional checks are needed before doing the elision.
    return makeExpression(constructor->getArg(0), shouldDelay, receiver);
  }
  assert(llvm::dyn_cast<clang::CXXMethodDecl>(constructor->getConstructor()));
  const clang::CXXMethodDecl* function = static_cast<const clang
      ::CXXMethodDecl*>(constructor->getConstructor());
  if (function->getParent()->isLambda() && constructor->getNumArgs() == 1) {
    // Some Lambda constructors are not seen as elidable. Nevertheless, we
    // use a custom translation mechanism there and bypass the constructor.
    return makeExpression(constructor->getArg(0), shouldDelay, receiver);
  }
  if (function->getTemplateSpecializationKind()
      >= clang::TSK_ImplicitInstantiation) {
    clang::FunctionTemplateSpecializationInfo* info
      = function->getTemplateSpecializationInfo();
    if (info)
      templateExtension=tkind_TTemplateInstance(
        _clangUtils->getTemplateExtension(info));
  };
  if (!templateExtension)
    templateExtension = tkind_TStandard();
  if (hasInstanceContext()) {
    if (!_tableForWaitingDeclarations.hasVisited(function)
         && function != _parents.getSFunctionDecl())
      unvisitedDecls().push_back(function);
    else {
      clang::Decl::Kind kindDecl = function->getDeclContext()->getDeclKind();
      if (kindDecl >= clang::Decl::firstRecord
          && kindDecl <= clang::Decl::lastRecord)
        _tableForWaitingDeclarations.ensureGeneration(
          static_cast<const clang::RecordDecl*>(function->getDeclContext()),
          unvisitedDecls());
    };
  }
  else if (shouldDelay && !*shouldDelay)
    *shouldDelay = !_tableForWaitingDeclarations.hasVisited(function)
         && function != _parents.getSFunctionDecl();

  qualified_name name = _clangUtils->makeQualifiedName(*function);
  if (strlen(name->decl_name) == 0) {
    free(const_cast<char*>(name->decl_name));
    name->decl_name = strdup("constructor-special");
  };
  if (isImplicitThisBare) {
    _rttiTable.addBareToQualification(name);
    // if (shouldDelay && !*shouldDelay)
    //   *shouldDelay = true;
  };
  clang::CXXConstructExpr::const_arg_iterator argEnd = constructor->arg_end();
  list /* expression */ arguments = NULL;
  ForwardReferenceList forwardArguments(arguments);
  clang::SourceLocation sloc = constructor->getExprLoc();
  location loc = makeLocation(constructor->getSourceRange());
  const char* temp = NULL;
  expression tmpvar;
  qual_type typ;
  if (hasImplicitThisStar) {
    expression lval = guard.releaseExpr ();
    expression address = expression_cons(loc,exp_node_Address(lval));
    tmpvar = address;
  }
  else {
    temp = mk_tmp_name();
    tmpvar = expression_cons(loc, exp_node_Address(
        expression_cons(copy_loc(loc), exp_node_Variable(
          variable_Local(qualified_name_cons(NULL,temp))))));
    typ = makeDefaultType(sloc, constructor->getType());
  };
  forwardArguments.insertContainer(tmpvar);
  for (clang::CXXConstructExpr::const_arg_iterator
      argIter = constructor->arg_begin(); argIter != argEnd; ++argIter) {
    exp_node argument = makeExpression(*argIter, shouldDelay,receiver);
    expression eargument = expression_cons(makeLocation(
          (*argIter)->getSourceRange()), argument);
    forwardArguments.insertContainer(eargument);
  };
  signature sig = _clangUtils->makeSignature(*constructor->getConstructor());
  exp_node call_node =
    exp_node_Static_call(
      name, sig, funkind_FKConstructor(true),
      arguments, templateExtension, false);
  expression call = expression_cons(copy_loc(loc),call_node);
  exp_node res = temp ? exp_node_Temporary(strdup(temp), typ,
      init_expr_Single_init(call), false) : call_node;
  return res;
}

exp_node FramacVisitor::makeDeleteExpression(
    const clang::CXXDeleteExpr* deleteExpr,
    bool* shouldDelay, /* statement */ list* receiver) {
  location loc = makeLocation(deleteExpr->getSourceRange());
  expression thisArgument =
    makeLocExpression(deleteExpr->getArgument(), shouldDelay, receiver);
  const clang::CXXRecordDecl* recordDecl =
    deleteExpr->getDestroyedType()->getAsCXXRecordDecl();
  /* statement */ list statements = NULL;

  if (deleteExpr->getOperatorDelete()
      && !deleteExpr->getOperatorDelete()->isImplicit()) {
    /* overloaded delete */
    const clang::FunctionDecl* function = deleteExpr->getOperatorDelete();
    if (hasInstanceContext()) {
      if (!_tableForWaitingDeclarations.hasVisited(function)
            && function != _parents.getSFunctionDecl())
        unvisitedDecls().push_back(function);
      else {
        clang::Decl::Kind kindDecl = function->getDeclContext()->getDeclKind();
        if (kindDecl >= clang::Decl::firstRecord
            && kindDecl <= clang::Decl::lastRecord)
          _tableForWaitingDeclarations.ensureGeneration(
            static_cast<const clang::RecordDecl*>(function->getDeclContext()),
            unvisitedDecls());
      };
    }
    else if (shouldDelay && !*shouldDelay)
      *shouldDelay = !_tableForWaitingDeclarations.hasVisited(function)
            && function != _parents.getSFunctionDecl();
    qualified_name name = _clangUtils->makeQualifiedName(
        *deleteExpr->getOperatorDelete());
    list /* expression */ arguments = cons_container(thisArgument, NULL);
    signature sig =
      _clangUtils->makeSignature(*deleteExpr->getOperatorDelete());
    // Call of overloaded delete
    statements =
      cons_container(
        statement_Expression(
          copy_loc(loc),
          expression_cons(
            copy_loc(loc),
            exp_node_Static_call(
              name,
              sig,
              funkind_FKFunction(),
              arguments,
              tkind_TStandard(),
              false))),
        statements);
  }
  else if (!deleteExpr->isArrayForm()) { // ::delete
    // Free
    statements =
      cons_container(
        statement_Expression(
          copy_loc(loc),
          expression_cons(
            copy_loc(loc),
            exp_node_Free(
              thisArgument))),
        statements);
  }
  else { // ::delete[]
    // Free for array
    statements =
      cons_container(
        statement_Expression(
          copy_loc(loc),
          expression_cons(
            copy_loc(loc),
            exp_node_FreeArray(
              thisArgument))),
        statements);
  }

  if(recordDecl) {
    clang::CXXDestructorDecl* destructor = recordDecl->getDestructor();
    if(destructor) {
      if (hasInstanceContext()) {
        if (!_tableForWaitingDeclarations.hasVisited(destructor)
               && destructor != _parents.getSFunctionDecl())
          unvisitedDecls().push_back(destructor);
        else {
          clang::Decl::Kind kindDecl = destructor->getDeclContext()
              ->getDeclKind();
          if (kindDecl >= clang::Decl::firstRecord
              && kindDecl <= clang::Decl::lastRecord) {
             _tableForWaitingDeclarations.ensureGeneration(
              static_cast<const clang::RecordDecl*>(
                destructor->getDeclContext()),
              unvisitedDecls());
            }
        };
      }
      else if (shouldDelay && !*shouldDelay) {
        *shouldDelay = !_tableForWaitingDeclarations.hasVisited(destructor)
            && destructor != _parents.getSFunctionDecl();
      }
      qualified_name name = _clangUtils->makeQualifiedName(*destructor);

      if (deleteExpr->isArrayForm()) {
        // "i"
        const char* loopVariableName = mk_tmp_name();
        // i
        expression loopVariableAsExpr =
          expression_cons(
            copy_loc(loc),
            exp_node_Variable(
              variable_Local(
                qualified_name_cons(
                  NULL,
                  loopVariableName))));
        expression zero = makeIntLiteral(loc,IULONGLONG,0);
        expression one = makeIntLiteral(loc,IULONGLONG,1);
        // length. As said above, should be dependent on the argument of free[]
        expression size = makeIntLiteral(loc,IULONGLONG,1);
        // n-1-i
        expression index =
          expression_cons(
            copy_loc(loc),
            exp_node_Binary_operator(
              BOMINUS,
              AKRVALUE,
              expression_cons(
                copy_loc(loc),
                exp_node_Binary_operator(
                  BOMINUS,
                  AKRVALUE,
                  size,
                  one)),
            loopVariableAsExpr));
        // p[n-1-i]
        expression nthElt =
          expression_cons(
            copy_loc(loc),
            exp_node_ArrayAccess(thisArgument, index));
        // TODO: verify if the following instruction is still needed
        // expression thisCopyArgument =
        //   makeLocExpression(deleteExpr->getArgument(),shouldDelay, receiver);
        // TODO : create a temp expression to avoid side effects
        list /* expression */ arguments =
          cons_container(
            expression_cons(
              copy_loc(loc),
              exp_node_Address(
                nthElt)),
            NULL);
        signature sig = _clangUtils->makeSignature(*destructor);
        // A::Dtor(&p[n-1-i])
        exp_node call_node =
          exp_node_Static_call(
            name,
            sig,
            funkind_FKDestructor(true),
            arguments,
            tkind_TStandard(),
            false);
        expression call = expression_cons(copy_loc(loc),call_node);
        // unsigned long long
        qual_type loopVariableType =
          qual_type_cons(
            NULL,
            typ_Int(
              IULONGLONG));
        // (unsigned long long)0;
        init_expr loopVariableInit =
          init_expr_Single_init(
            zero);
        // unsigned long long i = 0;
        list init =
          cons_container(
            init_declarator_cons(
              loopVariableName,
              loopVariableType,
              opt_some_container(
                loopVariableInit)),
            NULL);
        // ++i
        incr_statement incr =
          incr_statement_CExpression(
            expression_cons(
              copy_loc(loc),
              exp_node_Unary_operator(
                uokind_UOPreInc(),
                loopVariableAsExpr)));
        // i < length
        expression cond =
          expression_cons(
            copy_loc(loc),
            exp_node_Binary_operator(
              BOLESS,
              AKRVALUE,
              loopVariableAsExpr,
              size));
        // for(unsigned long long i = 0; i < length; ++i)
        //   A::Dtor(&p[n-1-i]);
        statement forStatement =
          statement_For(
            copy_loc(loc),
            init_statement_IVarDecl(
              init),
            opt_some_container(
              cond),
            incr,
            statement_Expression(
              copy_loc(loc),
              call),
            NULL);
        statements = cons_container(forStatement, statements);
      }
      else { //non array
        expression thisCopyArgument =
          makeLocExpression(deleteExpr->getArgument(), shouldDelay, receiver);
        // TODO : create a temp expression to avoid side effects
        list /* expression */ arguments =
          cons_container(thisCopyArgument, NULL);
        signature sig = _clangUtils->makeSignature(*destructor);
        exp_node call_node =
          exp_node_Static_call(
            name,
            sig,
            funkind_FKDestructor(true),
            arguments,
            tkind_TStandard(),
            false);
        statements =
          cons_container(
            statement_Expression(
              copy_loc(loc),
              expression_cons(
                copy_loc(loc),
                call_node)),
            statements);
      }
    }
  };
  return exp_node_GnuBody(statements);
}

exp_node FramacVisitor::makeNewExpression(
  const clang::CXXNewExpr* newExpr,
  bool* shouldDelay, /* statement */ list* receiver) {
  exp_node result = NULL;
  qual_type type =
    makeDefaultType(newExpr->getExprLoc(), newExpr->getAllocatedType());

  // First, we compute the address of the memory block where the object will
  // be stored. Various cases are possible, depending on the nature of
  // operator new used.

  // TODO: find a way to distinguish default placement new from custom one
  if (newExpr->getOperatorNew() && 
      !newExpr->getOperatorNew()->isReplaceableGlobalAllocationFunction() &&
      !newExpr->getOperatorNew()->isReservedGlobalPlacementOperator()) {
    // custom placement new. Just make a call to the corresponding function.
    qualified_name name
        = _clangUtils->makeQualifiedName(*newExpr->getOperatorNew());
    signature sig = _clangUtils->makeSignature(*newExpr->getOperatorNew());
    /* expression */ list arguments = NULL;
    ForwardReferenceList argumentsList(arguments);
    location loc = makeLocation(newExpr->getSourceRange());
    exp_node size_to_alloc =
      exp_node_Constant(
        compilation_constant_TypeCst(TCCSIZEOF,type->plain_type));
    if (newExpr->isArray()) {
      expression exp_size_elt = expression_cons(copy_loc(loc), size_to_alloc);
      // length
      expression exp_length;
#if CLANG_VERSION_MAJOR >= 9
      if (!newExpr->getArraySize().hasValue())
        exp_length = makeIntLiteral(copy_loc(loc), IINT, 0);
      else
        exp_length =
          makeLocExpression(*newExpr->getArraySize(), shouldDelay, receiver);
#else
      exp_length =
        makeLocExpression(newExpr->getArraySize(), shouldDelay, receiver);
#endif

      // size = length * sizeof(A)
      size_to_alloc =
        exp_node_Binary_operator(BOTIMES, AKRVALUE, exp_length, exp_size_elt);
    };
    argumentsList.insertContainer(expression_cons(copy_loc(loc),size_to_alloc));
    for (unsigned i = 0; i < newExpr->getNumPlacementArgs(); i++) {
      expression arg =
        makeLocExpression(newExpr->getPlacementArg(i), shouldDelay, receiver);
      argumentsList.insertContainer(arg);
    }
    // Call the explicit new operator
    // new(sizeof(A))
    result = exp_node_Static_call(
        name, sig, funkind_FKFunction(), arguments, tkind_TStandard(), false);
  } else if (newExpr->getNumPlacementArgs()) {
      // implicit placement new: just reuse the provided memory block
      // implicit placement new has exactly one argument, the address
      // of the memory block where the object should be put
      assert(newExpr->getNumPlacementArgs() == 1);
      result =
        makeExpression(newExpr->getPlacementArg(0), shouldDelay, receiver);
  } else if (!newExpr->isArray()) { // no placement, no array
      // malloc(sizeof(A))
      result = exp_node_Malloc(type->plain_type);
  } else {
#if CLANG_VERSION_MAJOR >= 9
      expression size;
      if (!newExpr->getArraySize().hasValue())
        size = makeIntLiteral(makeLocation(newExpr->getSourceRange()), IINT, 0);
      else
        size =
          makeLocExpression(*newExpr->getArraySize(), shouldDelay, receiver);
#else
      expression size =
        makeLocExpression(newExpr->getArraySize(), shouldDelay, receiver);
#endif
      // malloc(length * sizeof(A))
      result = exp_node_MallocArray(type->plain_type, size);
  }
  expression eresult =
    expression_cons(makeLocation(newExpr->getSourceRange()), result);
  type->plain_type = NULL;
  free_type(type);

  // Now, we have to initialize the content of the memory.

  if (newExpr->hasInitializer()) {
    const clang::CXXConstructExpr* constructor = newExpr->getConstructExpr();
    // Save the pointer returned by malloc in a fresh temporary variable
    const char* temp = mk_tmp_name();
    location loc = makeLocation(newExpr->getSourceRange());
    expression tmp_expr =
      expression_cons(
        copy_loc(loc),
        exp_node_Variable(variable_Local(qualified_name_cons(NULL, temp))));
    expression tmpvar =
      expression_cons(loc, exp_node_Assign(tmp_expr, eresult));
    if (!constructor) {
      // Initializing a scalar value, as in new int (10);
      // Translate that as a local definition + an assignment:
      // (int * tmp = malloc(sizeof(int)), *tmp = 10, tmp);
      result =
        exp_node_Temporary(
          strdup(temp),
          qual_type_cons(
            NULL,
            typ_Pointer(
              pkind_PDataPointer(
                makeDefaultType(
                  newExpr->getExprLoc(), newExpr->getAllocatedType())))),
          init_expr_Single_init(eresult), false);
      eresult = expression_cons(copy_loc(loc), result);
      expression init =
        makeLocExpression(newExpr->getInitializer(), shouldDelay, receiver);
      expression assign =
        expression_cons(
          copy_loc(loc),
          exp_node_Assign(
            expression_cons(
              copy_loc(loc),
              exp_node_Dereference(tmp_expr)),init));
      result = exp_node_Binary_operator(BOCOMMA, AKRVALUE, eresult, assign);
      eresult = expression_cons(copy_loc(loc), result);
      result =
        exp_node_Binary_operator(
          BOCOMMA, AKRVALUE, eresult, expression_dup(tmp_expr));
    }
    else {
      if(!newExpr->isArray()) {
          // *(tmp = (A*)malloc()) = initializer
        eresult =
          expression_cons(
            loc,
            exp_node_Dereference(
              expression_cons(
                copy_loc(loc),
                exp_node_PointerCast(
                  qual_type_cons(
                    NULL,
                    typ_LVReference(
                      pkind_PDataPointer(
                        makeDefaultType(
                          newExpr->getExprLoc(),
                          newExpr->getAllocatedType())))),
              reference_or_pointer_kind_RPKPointer(),
              tmpvar))));
        FramaCIRGenAction::ExpressionGuard guard(*this, eresult);
        // A::Ctor(...)
        exp_node call_node = makeConstructExpression(constructor, shouldDelay,
          receiver, true, false, guard);
        result =
          exp_node_Temporary(
            strdup(temp),
            qual_type_cons(
              NULL,
              typ_Pointer(
                pkind_PDataPointer(
                  makeDefaultType(
                    newExpr->getExprLoc(), newExpr->getAllocatedType())))),
            init_expr_Single_init(
              expression_cons(
                copy_loc(loc),
                call_node)),
            false);
      }
      else {
        // tmp = malloc()
        statement allocation = statement_Expression(copy_loc(loc), tmpvar);
        // "i"
        const char* loopVariableName = mk_tmp_name();
        // i
        expression loopVariableAsExpr =
          expression_cons(
            copy_loc(loc),
            exp_node_Variable(
              variable_Local(qualified_name_cons(NULL, loopVariableName))));
        // tmp[i]
        expression nthElt =
          expression_cons(
            copy_loc(loc),
            exp_node_ArrayAccess(expression_dup(tmp_expr), loopVariableAsExpr));
        FramaCIRGenAction::ExpressionGuard guard(*this, nthElt);
        // A::Ctor(&tmp[i])
        exp_node call_node = makeConstructExpression(constructor, shouldDelay,
          receiver, true, false, guard);
        expression call = expression_cons(copy_loc(loc),call_node);
        // unsigned long long
        qual_type loopVariableType =
          qual_type_cons(
            NULL,
            typ_Int(
              IULONGLONG));
        // (unsigned long long)0;
        init_expr loopVariableInit =
          init_expr_Single_init(makeIntLiteral(loc,IULONGLONG,0));
        // unsigned long long i = 0;
        list init =
          cons_container(
            init_declarator_cons(
              loopVariableName,
              loopVariableType,
              opt_some_container(
                loopVariableInit)),
            NULL);
        // ++i
        incr_statement incr =
          incr_statement_CExpression(
            expression_cons(
              copy_loc(loc),
              exp_node_Unary_operator(
                uokind_UOPreInc(),
                loopVariableAsExpr)));
        // length
        expression size =
#if CLANG_VERSION_MAJOR >= 9
          (!newExpr->getArraySize().hasValue())
            ? makeIntLiteral(copy_loc(loc), IINT, 0)
            : makeLocExpression(
                *newExpr->getArraySize(),
                shouldDelay,
                receiver);
#else
          expression_cons(
            copy_loc(loc),
            makeExpression(
              newExpr->getArraySize(),
              shouldDelay,
              receiver));
#endif
        // i < length
        expression cond =
          expression_cons(
            copy_loc(loc),
            exp_node_Binary_operator(
              BOLESS,
              AKRVALUE,
              loopVariableAsExpr,
              size));
        // for(unsigned long long i = 0; i < length; ++i)
        //   A::Ctor(&tmp[i]);
        statement forStatement =
          statement_For(
            copy_loc(loc),
            init_statement_IVarDecl(
              init),
            opt_some_container(
              cond),
            incr,
            statement_Expression(
              copy_loc(loc),
              call),
            NULL);
        list statements = NULL;
        statements =
          cons_container(
            statement_Expression(
              copy_loc(loc),
              expression_cons(
                copy_loc(loc),
                exp_node_Variable(
                  variable_Local(
                    qualified_name_cons(
                      NULL,
                      temp))))),
            statements);
        statements = cons_container(forStatement, statements);
        statements = cons_container(allocation, statements);
        statements =
          cons_container(
            statement_VarDecl(
              copy_loc(loc),
              strdup(temp),
              qual_type_cons(
                NULL,
                typ_Pointer(
                  pkind_PDataPointer(
                    makeDefaultType(
                      newExpr->getExprLoc(),
                      newExpr->getAllocatedType())))),
              opt_none()),
            statements);
        /*
         * statements:
         * A* tmp = malloc(length * sizeof(A));
         * for(unsigned long long i = 0; i < length; ++i)
         *   A::Ctor(&tmp[i]);
         * tmp;
         */
        // ({statements})
        result = exp_node_GnuBody(statements);
      }
    };
  };
  return result;
}

void FramacVisitor::ensureBuiltinDeclaration(
  unsigned builtinID, const clang::FunctionDecl* fd, bool doesForceVariadic)
{ if (!isGeneratedBuiltin(builtinID)) {
    const char* name = copy_string(fd->getNameAsString ());
    clang::SourceLocation sloc = fd->getLocation();
    location loc = makeLocation(fd->getSourceRange());
    qual_type return_type =
      makeDefaultExternalNameType(sloc, fd->getReturnType());
    list /*arg_decl*/ prms = NULL;
    ForwardReferenceList params(prms);
    if (builtinID >= clang::Builtin::BI__atomic_load
        && builtinID <= clang::Builtin::BI__atomic_nand_fetch
        && return_type->plain_type->tag_typ == VOID) {
      free_typ(return_type->plain_type);
      return_type->plain_type = typ_Int(IINT);
      arg_decl cdecl = (arg_decl)malloc(sizeof(*cdecl));
      cdecl->arg_name = strdup("__frama_c_arg_0");
      cdecl->arg_type = qual_type_cons(NULL, typ_Pointer(
        pkind_PDataPointer(qual_type_cons(NULL, typ_Void()))));
      cdecl->arg_loc = copy_loc(loc);
      params.insertContainer(cdecl);
    }
    else if (builtinID == clang::Builtin::BI__builtin_va_end
          || builtinID == clang::Builtin::BI__builtin_va_start) {
      arg_decl cdecl = (arg_decl)malloc(sizeof(*cdecl));
      const clang::ParmVarDecl *prm = fd->getParamDecl(0);
      if (prm->getNameAsString().size() > 0)
        cdecl->arg_name = copy_string(prm->getNameAsString());
      else
        cdecl->arg_name = strdup("__frama_c_arg_0");
      cdecl->arg_type = qual_type_cons(NULL, typ_Named(
        qualified_name_cons(NULL, strdup("__builtin_va_list")), true));
      cdecl->arg_loc = makeLocation(prm->getSourceRange());
      params.insertContainer(cdecl);
    } else {
      int i = 0;
      clang::FunctionDecl::param_const_iterator stop = fd->param_end();
      for (clang::FunctionDecl::param_const_iterator it = fd->param_begin(); 
           it!=stop;it++) {
        if (it!=fd->param_begin() || !doesForceVariadic
            || !(*it)->getOriginalType()->isVoidType()) {
        std::string name = (*it)->getNameAsString();
        if (name.size() == 0) {
          std::ostringstream out;
          out << "__frama_c_arg_" << i++;
          name = out.str();
        };
        clang::SourceLocation sloc = (*it)->getLocation();
        qual_type prm_type =
          makeDefaultExternalNameType(sloc, (*it)->getOriginalType());
        location loc = makeLocation((*it)->getSourceRange());
        params.insertContainer(arg_decl_cons(prm_type,copy_string(name),loc));
        }
      }
    }
    decl_or_impl_name decl_name = decl_or_impl_name_Declaration(name);
    translation_unit_decl func =
      translation_unit_decl_Function(
        decl_name, funkind_FKFunction(), loc, return_type, prms,
        opt_none() /* body */, true /* fd->isExternC() */, false,
        doesForceVariadic || fd->isVariadic(), tkind_TStandard(),
        false /* has_further_definition */,
        opt_none() /* throws */,
        opt_none() /* contract */);
    if (_clangUtils->isExternCContext(_lexicalContextForPostVisit)
         && _clangUtils->isExternCContext(_semanticContextForPostVisit))
      _globals.insertContainer(func);
    else
      _globals.insertBeforeContainer(func);
    if (builtinID < clang::Builtin::FirstTSBuiltin)
      setGeneratedBuiltin(builtinID);
  };
}

bool FramacVisitor::is_lambda_call(const clang::CallExpr* call) {
  if (call->getStmtClass() == clang::Stmt::CXXOperatorCallExprClass) {
    const clang::CXXOperatorCallExpr* op =
      llvm::dyn_cast<clang::CXXOperatorCallExpr>(call);
    if (op->getOperator() == clang::OO_Call) {
      if (call->getNumArgs() > 0) {
        clang::QualType typ = call->getArg(0)->getType();
        const clang::CXXRecordDecl* rec = typ->getAsCXXRecordDecl();
        return (rec && rec->isLambda());
      }
    }
  }
  return false;
}

exp_node FramacVisitor::makeLambdaCallExpression(
  const clang::CallExpr* call, bool* shouldDelay, list* receiver,
  FramaCIRGenAction::ExpressionGuard& guard) {
  list arguments = NULL;
  clang::CallExpr::const_arg_iterator beg = call->arg_begin();
  clang::CallExpr::const_arg_iterator it = call->arg_end();
  expression lambda_obj = makeLocExpression(*beg, shouldDelay, receiver);
  beg++;
  while (beg < it) {
    it -= 1;
    expression arg = makeLocExpression(*it, shouldDelay, receiver);
    arguments = cons_container(arg, arguments);
  }
  exp_node result = exp_node_Lambda_call(lambda_obj, arguments);
  return
    convert_result(guard, call->getCallReturnType(*_context), result, call);
}

exp_node FramacVisitor::makeCallExpression(
  const clang::CallExpr* callExpr, bool* shouldDelay,
  /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard) {
  funkind fkind;
  if (is_lambda_call(callExpr))
    return makeLambdaCallExpression(callExpr,shouldDelay,receiver,guard);
  const clang::FunctionDecl* fd = callExpr->getDirectCallee();
  if (fd) {
    clang::Decl::Kind kind = fd->getDeclKind();
    if (kind == clang::Decl::CXXConstructor)
      fkind = funkind_FKConstructor(true);
    else if (kind == clang::Decl::CXXDestructor)
      fkind = funkind_FKDestructor(true);
    else if ((kind >= clang::Decl::firstCXXMethod)
        && (kind <= clang::Decl::lastCXXMethod)) {
      if (fd->getCanonicalDecl()->getStorageClass() != clang::SC_Static)
        fkind = _clangUtils->cv_meth(
          static_cast<const clang::CXXMethodDecl*>(fd));
      else
        fkind = funkind_FKFunction();
    }
    else
      fkind = funkind_FKFunction();
    unsigned builtinID = fd->getBuiltinID();
    if (builtinID > 0) {
      ensureBuiltinDeclaration(builtinID, fd);
      _tableForWaitingDeclarations.addDeclaration(fd,_globals);
      _instanceContexts.removeUnvisited(fd);
    }
  }
  else if (clang::CXXOperatorCallExpr::classof(callExpr))
    /* TODO: check whether an operator can have cv qualification */
    fkind = funkind_FKMethod(NULL);
  else fkind = funkind_FKFunction ();
  clang::CallExpr::const_arg_iterator argIterEnd = callExpr->arg_end();
  list /* expression */ arguments = NULL;
  ForwardReferenceList forwardArguments(arguments);
  bool isFirstObject = (fkind->tag_funkind != FKFUNCTION);
  for (clang::CallExpr::const_arg_iterator argIter=callExpr->arg_begin();
      argIter != argIterEnd; ++argIter) {
    expression arg = makeLocExpression(*argIter, shouldDelay,receiver);
    if (isFirstObject) {
      arg =
        expression_cons(
          makeLocation((*argIter)->getSourceRange()),
          exp_node_Address(arg));
    };
    forwardArguments.insertContainer(arg);
    isFirstObject = false;
  };
  const clang::FunctionDecl* directCall = callExpr->getDirectCallee();
  if (directCall) {
    tkind templateExtension = NULL;
    if (directCall->getTemplateSpecializationKind()
        >= clang::TSK_ImplicitInstantiation) {
      clang::FunctionTemplateSpecializationInfo* info
          = directCall->getTemplateSpecializationInfo();
      if (info)
        templateExtension =
          tkind_TTemplateInstance(_clangUtils->getTemplateExtension(info));
    };
    if (!templateExtension)
      templateExtension = tkind_TStandard();
    qualified_name name = _clangUtils->makeQualifiedName(*directCall);
    if (fkind->tag_funkind == FKCONSTRUCTOR && strlen(name->decl_name) == 0) {
      free(const_cast<char*>(name->decl_name));
      name->decl_name = strdup("constructor-special");
    };
    if (hasInstanceContext()) {
      if (!_tableForWaitingDeclarations.hasVisited(directCall)
            && directCall != _parents.getSFunctionDecl())
        unvisitedDecls().push_back(directCall);
      else {
        clang::Decl::Kind kindDecl = directCall->getDeclContext()->getDeclKind();
        if (kindDecl >= clang::Decl::firstRecord
            && kindDecl <= clang::Decl::lastRecord)
          _tableForWaitingDeclarations.ensureGeneration(
            static_cast<const clang::RecordDecl*>(directCall->getDeclContext()),
            unvisitedDecls());
      };
    }
    else if (shouldDelay && !*shouldDelay)
      *shouldDelay = !_tableForWaitingDeclarations.hasVisited(directCall)
            && directCall != _parents.getSFunctionDecl();

    signature sig = _clangUtils->makeSignature(*directCall);
    exp_node result =
      exp_node_Static_call(
        name, sig, fkind, arguments,
        templateExtension, directCall->isInExternCContext());
    return
      convert_result(
        guard,callExpr->getCallReturnType(*_context),result,callExpr);
  };
  if (callExpr->getCallee()->getStmtClass()
      == clang::Stmt::CXXPseudoDestructorExprClass)
    return exp_node_Constant(compilation_constant_IntCst(IINT,
            ICSTATICCONST, 0));
  expression call =
    makeLocExpression(callExpr->getCallee(), shouldDelay,receiver);
  return
    convert_result(
      guard,
      callExpr->getCallReturnType(*_context),
      exp_node_Dynamic_call(fkind, call, arguments),
      callExpr);
}

exp_node FramacVisitor::makeMemberCallExpression(
  const clang::CXXMemberCallExpr* callExpr, bool* shouldDelay,
  /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard)
{ 
  /*
    There are 4 kinds of member calls:
    - direct call to a non-static, non-virtual function (just need to add the
      this argument at the beginning of the list)
    - direct call to a virtual function (this argument + retrieve entry in
      virtual methode table)
    - call via a pointer-to-member to non-virtual function
    - call via a pointer-to-member to virtual function (currently unsupported)
   */
  clang::CXXMemberCallExpr::const_arg_iterator argIterEnd = callExpr->arg_end();
  const clang::Expr* thisArgument = callExpr->getImplicitObjectArgument();
  list /* expression */ arguments = NULL;
  ForwardReferenceList forwardArguments(arguments);
  const clang::Expr* callee = callExpr->getCallee()->IgnoreParens();
  // directCall will be NULL for pointer-to-member calls
  const clang::CXXMethodDecl* directCall = callExpr->getMethodDecl();
  // NB: as said above, pointer-to-member are assumed to be non-virtual.
  bool isVirtualCall = directCall ? directCall->isVirtual() : false;
  // even if the function is virtual, if we have qualified lookup, we'll end
  // up calling a specific version, without VT lookup.
  if (isVirtualCall) {
    assert(llvm::dyn_cast<const clang::MemberExpr>(callee));
    isVirtualCall =
      !static_cast<const clang::MemberExpr*>(callee)->hasQualifier();
  }
  // first, translate the receiver argument (i.e. this)
  expression argument = makeLocExpression(thisArgument, shouldDelay);
  // clang doc says that callee is a member expr
  // in fact, it contains the information whether we
  // have x.f(),  x->f() x.*f() or x->*f()
  clang::Stmt::StmtClass kind = callee->getStmtClass();
  assert (kind == clang::Stmt::BinaryOperatorClass
          || kind == clang::Stmt::MemberExprClass);
    // pointer to member call
  if (kind == clang::Stmt::BinaryOperatorClass) {
    assert(llvm::dyn_cast<const clang::BinaryOperator>(callee));
    const clang::BinaryOperator* binop =
      static_cast<const clang::BinaryOperator*>(callee);
    switch(binop->getOpcode())
      {
        case clang::BO_PtrMemD:
          argument =
            expression_cons(makeLocation(callee->getSourceRange()),
                            exp_node_Address(argument));
        case clang::BO_PtrMemI:
          break;
        default:
          std::cerr << "Unexpected opcode in method call: ";
          callee->dump();
          std::cerr << std::endl;
          exit(2);
      }
  } else {
    // normal call (either static or virtual)
    assert(llvm::dyn_cast<const clang::MemberExpr>(callee));
    const clang::MemberExpr* callee_member
      = static_cast<const clang::MemberExpr*>(callee);
    if(!callee_member->isArrow()) {
      argument =
        expression_cons(
          makeLocation(callee->getSourceRange()),
          exp_node_Address(argument));
    }
  }
  // for virtual calls, the receiver is still treated separately
  if (!isVirtualCall) forwardArguments.insertContainer(argument);

  // Now translate all the arguments
  for (clang::CXXMemberCallExpr::const_arg_iterator
      argIter = callExpr->arg_begin(); argIter != argIterEnd; ++argIter) {
    expression argument = makeLocExpression(*argIter, shouldDelay);
    forwardArguments.insertContainer(argument);
  };

  // Now, find which function to call
  // First, check whether we are in a template instantiation
  tkind templateExtension = NULL;
  if (directCall && directCall->getTemplateSpecializationKind()
      >= clang::TSK_ImplicitInstantiation) {
    clang::FunctionTemplateSpecializationInfo* info
      = directCall->getTemplateSpecializationInfo();
    if (info)
      templateExtension =
        tkind_TTemplateInstance(_clangUtils->getTemplateExtension(info));
  };
  if (!templateExtension) templateExtension = tkind_TStandard();
  if (!directCall) {
    // pointer to member call: we have a binary operator, and the
    // function pointer is the rhs part
    assert(llvm::dyn_cast<const clang::BinaryOperator>(callee) && _context);
    const clang::BinaryOperator* binop =
      static_cast<const clang::BinaryOperator*>(callee);
    expression call = makeLocExpression(binop->getRHS());
    return
      convert_result(
        guard,
        callExpr->getCallReturnType(*_context),
        exp_node_Dynamic_call(funkind_FKMethod(NULL), call, arguments),
        callExpr);

  }
  // direct call

  // Update tableForwaitingdeclarations as needed to provide functions
  // definitions in a suitable order.
  if (hasInstanceContext()) {
    if (!_tableForWaitingDeclarations.hasVisited(directCall)
        && directCall != _parents.getSFunctionDecl())
      unvisitedDecls().push_back(directCall);
    else {
      clang::Decl::Kind kindDecl =
        directCall->getDeclContext()->getDeclKind();
      if (kindDecl >= clang::Decl::firstRecord
          && kindDecl <= clang::Decl::lastRecord)
        _tableForWaitingDeclarations.ensureGeneration(
          static_cast<const clang::RecordDecl*>(
            directCall->getDeclContext()),
          unvisitedDecls());
    };
  }
  else if (shouldDelay && !*shouldDelay)
    *shouldDelay = !_tableForWaitingDeclarations.hasVisited(directCall)
      && directCall != _parents.getSFunctionDecl();
  
  qualified_name name = _clangUtils->makeQualifiedName(*directCall);
  signature sig = _clangUtils->makeSignature(*directCall);
  clang::QualType const& ret = callExpr->getCallReturnType(*_context);
  if (!isVirtualCall) {
    // static call: we just have a normal function call
    return convert_result(
      guard,ret,
      exp_node_Static_call(
        name, sig,
        _clangUtils->cv_meth(static_cast<const clang::CXXMethodDecl*>(
            directCall)), arguments, templateExtension, false),
      callExpr);
  };

  // virtual call: this is in fact an indirect call.
  // Retrieve appropriate pointer from VMT
  assert(templateExtension->tag_tkind == TSTANDARD);
  free(templateExtension);
  templateExtension = NULL;
  exp_node result =
    exp_node_Virtual_call(
      name, sig, _clangUtils->cv_meth(static_cast<const clang::CXXMethodDecl*>(
        directCall)), argument, arguments, 0, NULL, NULL);
  const_cast<RTTITable&>(_rttiTable).retrieveMethodIndex(*_clangUtils,
      callExpr->getMethodDecl()->getParent(), callExpr->getMethodDecl(),
      &result->cons_exp_node.Virtual_call.method_index,
      &result->cons_exp_node.Virtual_call.shift_object,
      &result->cons_exp_node.Virtual_call.shift_pvmt);
  return convert_result(guard,ret,result, callExpr);
}

exp_node
FramacVisitor::makeBaseToDerivedPointerCastExpression(
    const clang::CXXRecordDecl* base, qual_type baseType,
    const clang::CXXRecordDecl* derived, qual_type derivedType,
    expression expr) {
  assert(base && derived);
  RTTITable::InheritancePath inheritancePath;
  RTTITable::VirtualInheritancePath virtualInheritancePath(NULL, 0);
  _rttiTable.retrieveInheritancePathBetween(derived, base,
      inheritancePath, virtualInheritancePath, *_clangUtils);
  assert(!virtualInheritancePath.first);
  int sizeInheritancePath = (int) inheritancePath.size()-1;
  assert(sizeInheritancePath >= 0);
  exp_node nodeResult = exp_node_ShiftPointerCast(
      derivedType, baseType, reference_or_pointer_kind_RPKPointer(), expr);
  while (--sizeInheritancePath >= 0) {
    const clang::CXXRecordDecl
      *localDerived = inheritancePath[sizeInheritancePath].first;
    tkind derived_kind = _clangUtils->makeTemplateKind(localDerived);
    qual_type localDerivedType =
      qual_type_cons(
        NULL,
        typ_Pointer(
          pkind_PDataPointer(
            qual_type_cons(
              NULL,
              typ_Struct(
                _clangUtils->makeQualifiedName(*localDerived),derived_kind)))));
    exp_node tmpResult = exp_node_ShiftPointerCast(
      localDerivedType, qual_type_dup(localDerivedType),
      reference_or_pointer_kind_RPKPointer(),
      expression_cons(copy_loc(expr->eloc), nodeResult));
    qual_type tmp=nodeResult->cons_exp_node.ShiftPointerCast.cast_type;
    nodeResult->cons_exp_node.ShiftPointerCast.cast_type
      = tmpResult->cons_exp_node.ShiftPointerCast.cast_type;
    tmpResult->cons_exp_node.ShiftPointerCast.cast_type = tmp;
    nodeResult = tmpResult;
  };
  return nodeResult;
}

exp_node FramacVisitor::makeBaseToDerivedReferenceCastExpression(
    const clang::CXXRecordDecl* base, qual_type baseType,
    const clang::CXXRecordDecl* derived, qual_type derivedType,
    expression expr) {
  assert(base && derived);
  RTTITable::InheritancePath inheritancePath;
  RTTITable::VirtualInheritancePath virtualInheritancePath(NULL, 0);
  _rttiTable.retrieveInheritancePathBetween(derived, base,
      inheritancePath, virtualInheritancePath, *_clangUtils);
  assert(!virtualInheritancePath.first);
  int sizeInheritancePath = (int) inheritancePath.size()-1;
  assert(sizeInheritancePath >= 0);
  exp_node nodeResult = exp_node_ShiftPointerCast(
      qual_type_cons(NULL, typ_LVReference(pkind_PDataPointer(derivedType))),
      baseType, reference_or_pointer_kind_RPKReference(), expr);
  while (--sizeInheritancePath >= 0) {
    const clang::CXXRecordDecl
      *localDerived = inheritancePath[sizeInheritancePath].first;
    tkind derived_kind = _clangUtils->makeTemplateKind(localDerived);
    qual_type localDerivedType =
      qual_type_cons(
        NULL,
        typ_LVReference(
          pkind_PDataPointer(
            qual_type_cons(
              NULL,
              typ_Struct(
                _clangUtils->makeQualifiedName(*localDerived),derived_kind)))));
    exp_node tmpResult = exp_node_ShiftPointerCast(
      localDerivedType,
      qual_type_dup(localDerivedType->plain_type->cons_typ.LVReference
          .kind->cons_pkind.PDataPointer.subtype),
      reference_or_pointer_kind_RPKReference(),
      expression_cons(copy_loc(expr->eloc), nodeResult));
    qual_type tmp=nodeResult->cons_exp_node.ShiftPointerCast.cast_type;
    nodeResult->cons_exp_node.ShiftPointerCast.cast_type
      = tmpResult->cons_exp_node.ShiftPointerCast.cast_type;
    tmpResult->cons_exp_node.ShiftPointerCast.cast_type = tmp;
    nodeResult = tmpResult;
  };
  return nodeResult;
}

exp_node FramacVisitor::makeDerivedToBaseCastExpression(
  ptr_or_ref kind,
  const clang::CXXRecordDecl* derived, qual_type baseType,
  const clang::CXXRecordDecl* base, expression expr, bool* shouldDelay)
{ assert(base && derived);
  if (hasInstanceContext()) {
    _tableForWaitingDeclarations.ensureGeneration(derived, unvisitedDecls());
    _tableForWaitingDeclarations.ensureGeneration(base, unvisitedDecls());
  }
  else if (shouldDelay && !*shouldDelay) {
    *shouldDelay = !_tableForWaitingDeclarations.hasVisited(derived)
        || !_tableForWaitingDeclarations.hasVisited(base);
  };
  RTTITable::InheritancePath inheritancePath;
  RTTITable::VirtualInheritancePath virtualInheritancePath(NULL, 0);
  _rttiTable.retrieveInheritancePathBetween(
    derived, base, inheritancePath, virtualInheritancePath, *_clangUtils);

  exp_node nodeResult = NULL;
  int sizeInheritancePath = (int) inheritancePath.size()-1;
  // if we don't have a virtual base, the non-virtual inheritance path
  // cannot be empty
  assert(virtualInheritancePath.first || sizeInheritancePath >= 0);
  // if the base class is part of a virtual base of derived (either
  // directly a virtual base, or a class the virtual base inherits from),
  // we first perform an offset computation, potentially followed by
  // a sequence of non-virtual casts
  if (virtualInheritancePath.first) {
    // const clang::ClassTemplateSpecializationDecl* TSD = NULL;
    tkind tk = _clangUtils->makeTemplateKind(derived);
    auto pk_derived =
      pkind_PDataPointer(
        qual_type_cons(
          NULL, typ_Struct(_clangUtils->makeQualifiedName(*derived),tk)));
    auto t_derived =
      kind == PTR ? typ_Pointer(pk_derived) : typ_LVReference(pk_derived);
    qual_type derivedType = qual_type_cons(NULL, t_derived);
    const clang::CXXRecordDecl* derivedClass = virtualInheritancePath.first;
    qual_type localDerivedType = baseType;
    if (sizeInheritancePath >= 0) {
      localDerivedType = qual_type_dup(derivedType);
    };
    auto rpk =
      kind == PTR ?
      reference_or_pointer_kind_RPKVirtualBasePointer(
        virtualInheritancePath.second, derivedType, false) :
      reference_or_pointer_kind_RPKVirtualBaseReference(
        virtualInheritancePath.second, derivedType);
    nodeResult = exp_node_PointerCast(localDerivedType, rpk, expr);
    if (virtualInheritancePath.second < 0) {
      auto id = nodeResult->cons_exp_node.PointerCast.ref_pointer;
      auto idx =
        kind == PTR ?
        &id->cons_reference_or_pointer_kind.RPKVirtualBasePointer.base_index:
        &id->cons_reference_or_pointer_kind.RPKVirtualBaseReference.base_index;
      const_cast<RTTITable&>(_rttiTable).retrieveBaseIndex(
        *_clangUtils,
        derived, const_cast<clang::CXXRecordDecl*>(derivedClass), idx);
    }
  };
  // now compute the non-virtual part of the pointer cast.
  if (sizeInheritancePath >= 0) {
    auto exp = nodeResult?expression_cons(copy_loc(expr->eloc),nodeResult):expr;
    auto rpk =
      kind == PTR ?
      reference_or_pointer_kind_RPKStaticBasePointer ():
      reference_or_pointer_kind_RPKStaticBaseReference ();
    nodeResult = exp_node_PointerCast(baseType, rpk, exp);
  }
  for (int index = 0; index < sizeInheritancePath; ++index) {
    const clang::CXXRecordDecl
      *localBase = inheritancePath[index].first;
    auto tk = _clangUtils->makeTemplateKind(localBase);
    auto pk_data =
      pkind_PDataPointer(
        qual_type_cons(
          NULL,typ_Struct(_clangUtils->makeQualifiedName(*localBase), tk)));
    auto typ =
      kind == PTR ? typ_Pointer(pk_data) : typ_LVReference(pk_data);
    qual_type localBaseType = qual_type_cons(NULL,typ);
    auto rpk =
      kind == PTR ?
      reference_or_pointer_kind_RPKStaticBasePointer() :
      reference_or_pointer_kind_RPKStaticBaseReference();
    exp_node tmpResult =
      exp_node_PointerCast(
        localBaseType, rpk, nodeResult->cons_exp_node.PointerCast.sub);
    nodeResult->cons_exp_node.PointerCast.sub =
        expression_cons(copy_loc(expr->eloc), tmpResult);
  };
  return nodeResult;
}

exp_node FramacVisitor::makeCastExpression(
  const clang::CastExpr* castExpr,
  bool* shouldDelay, /* statement */ list* receiver,
  FramaCIRGenAction::ExpressionGuard& guard) {
  expression subExpr =
    makeLocExpression(castExpr->getSubExpr(), shouldDelay, receiver);
  qual_type resultType =
    makeDefaultType(castExpr->getExprLoc(), castExpr->getType());
  switch (castExpr->getCastKind()) {
    case clang::CK_BitCast:
      return guard.setAssignResult(exp_node_Unary_operator(
           uokind_UOCastC(resultType),subExpr), castExpr);
    case clang::CK_LValueBitCast:
      return guard.setAssignResult(exp_node_Dereference(
        expression_cons(copy_loc(subExpr->eloc), exp_node_Unary_operator(
          uokind_UOCastC(qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(
            resultType)))), expression_cons(copy_loc(subExpr->eloc),
              exp_node_Address(subExpr))))), castExpr);
    case clang::CK_ToUnion:
    case clang::CK_VectorSplat:
    case clang::CK_CPointerToObjCPointerCast:
    case clang::CK_BlockPointerToObjCPointerCast:
    case clang::CK_AnyPointerToBlockPointerCast:
    case clang::CK_ObjCObjectLValueCast:
    case clang::CK_ARCProduceObject:
    case clang::CK_ARCConsumeObject:
    case clang::CK_ARCReclaimReturnedObject:
    case clang::CK_ARCExtendBlockObject:
    case clang::CK_AtomicToNonAtomic:
    case clang::CK_NonAtomicToAtomic:
    case clang::CK_CopyAndAutoreleaseBlockObject:
    case clang::CK_BuiltinFnToFnPtr:
      std::cerr << "Unsupported cast:";
#if CLANG_VERSION_MAJOR >= 11
      castExpr->dump(llvm::errs(), *_context);
#else
      castExpr->dump(llvm::errs(), _context->getSourceManager());
#endif
      std::cerr << "\nAborting\n";
      exit(2);
    case clang::CK_FloatingRealToComplex:
    case clang::CK_FloatingComplexToReal:
    case clang::CK_FloatingComplexToBoolean:
    case clang::CK_FloatingComplexCast:
    case clang::CK_FloatingComplexToIntegralComplex:
    case clang::CK_IntegralRealToComplex:
    case clang::CK_IntegralComplexToReal:
    case clang::CK_IntegralComplexToBoolean:
    case clang::CK_IntegralComplexCast:
    case clang::CK_IntegralComplexToFloatingComplex:
      std::cerr << "Unsupported context cast:";
#if CLANG_VERSION_MAJOR >= 11
      castExpr->dump(llvm::errs(), *_context);
#else
      castExpr->dump(llvm::errs(), _context->getSourceManager());
#endif
      std::cerr << "\nAborting\n";
      exit(2);
    case clang::CK_ToVoid:
      return
        guard.setAssignResult(
          exp_node_Unary_operator(uokind_UOCastToVoid(), subExpr), castExpr);
    case clang::CK_LValueToRValue:
      // does not exactly denote a cast from "reference to T" to "T":
      // we need to use another indicator to introduce the appropriate
      // transformation, see ClangUtils::lvalHasRefType for more information
    case clang::CK_NoOp:
      return
        guard.setAssignResult(
          exp_node_Unary_operator(uokind_UOCastNoEffect(resultType), subExpr),
          castExpr);
    case clang::CK_BaseToDerived:
      { qual_type baseType =
          makeDefaultType(
            castExpr->getSubExpr()->getExprLoc(),
            castExpr->getSubExpr()->getType());
        if (castExpr->getType()->isPointerType())
          /* isArrayType(), isFunctionType(), isPointerType(),
             isReferenceType(), isRecordType(), isUnionType(),
             isEnumeralType(), isMemberPointerType() */
          return guard.setAssignResult(
            makeBaseToDerivedPointerCastExpression(
              castExpr->getSubExpr()->getType()->getPointeeCXXRecordDecl(),
              baseType, castExpr->getType()->getPointeeCXXRecordDecl(),
              resultType, subExpr), castExpr);
        return guard.setAssignResult(
          makeBaseToDerivedReferenceCastExpression(
            castExpr->getSubExpr()->getType()->getAsCXXRecordDecl(), baseType,
            castExpr->getType()->getAsCXXRecordDecl(), resultType, subExpr),
          castExpr);
      }
    case clang::CK_UncheckedDerivedToBase:
    case clang::CK_DerivedToBase:
      if (castExpr->getType()->isPointerType())
        /* isArrayType(), isFunctionType(), isPointerType(),
           isReferenceType(), isRecordType(), isUnionType(),
           isEnumeralType(), isMemberPointerType() */
          return guard.setAssignResult(
            makeDerivedToBaseCastExpression(
              PTR,
              castExpr->getSubExpr()->getType()->getPointeeCXXRecordDecl(),
              resultType, castExpr->getType()->getPointeeCXXRecordDecl(),
              subExpr, shouldDelay),
            castExpr);
        return guard.setAssignResult(
          makeDerivedToBaseCastExpression(
            REF,
            castExpr->getSubExpr()->getType()->getAsCXXRecordDecl(),
            qual_type_cons(NULL, typ_LVReference(pkind_PDataPointer(resultType))),
            castExpr->getType()->getAsCXXRecordDecl(), subExpr,
            shouldDelay),
          castExpr);
    case clang::CK_ArrayToPointerDecay:
    case clang::CK_FunctionToPointerDecay:
    case clang::CK_NullToMemberPointer:
    case clang::CK_NullToPointer:
      if (castExpr->getType()->isReferenceType())
        /* isArrayType(), isFunctionType(), isPointerType(),
           isReferenceType(), isRecordType(), isUnionType(),
           isEnumeralType(), isMemberPointerType() */
        return guard.setAssignResult(exp_node_PointerCast(resultType,
              reference_or_pointer_kind_RPKReference(), subExpr), castExpr);
      return guard.setAssignResult(exp_node_PointerCast(resultType,
            reference_or_pointer_kind_RPKPointer(), subExpr), castExpr);
    case clang::CK_IntegralToPointer:
    case clang::CK_ReinterpretMemberPointer:
      return guard.setAssignResult(exp_node_PointerCast(resultType,
            reference_or_pointer_kind_RPKPointer(), subExpr), castExpr);
    case clang::CK_MemberPointerToBoolean:
    case clang::CK_PointerToBoolean:
    case clang::CK_IntegralToBoolean:
    case clang::CK_FloatingToBoolean:
      return guard.setAssignResult(exp_node_Unary_operator(
          uokind_UOCastInteger(resultType, IBOOL)/*, AKRVALUE*/, subExpr),
        castExpr);
    case clang::CK_PointerToIntegral:
    case clang::CK_IntegralCast:
    case clang::CK_IntegralToFloating:
    case clang::CK_FloatingToIntegral:
    case clang::CK_FloatingCast:
      if (resultType->plain_type->tag_typ==ENUM)
        return guard.setAssignResult(exp_node_Unary_operator(
          uokind_UOCastEnum(resultType, resultType->plain_type
            ->cons_typ.Enum.kind), /*AKRVALUE,*/ subExpr), castExpr);
      if (resultType->plain_type->tag_typ==INT)
        return guard.setAssignResult(exp_node_Unary_operator(
          uokind_UOCastInteger(resultType, resultType->plain_type
            ->cons_typ.Int.kind), /* AKRVALUE,*/ subExpr), castExpr);
      if (resultType->plain_type->tag_typ==FLOAT)
        return guard.setAssignResult(exp_node_Unary_operator(
          uokind_UOCastFloat(resultType, resultType->plain_type
            ->cons_typ.Float.kind), /* AKRVALUE,*/ subExpr), castExpr);
      return guard.setAssignResult(exp_node_Unary_operator(
          uokind_UOCastC(resultType),subExpr), castExpr);
    case clang::CK_UserDefinedConversion: /* should be translated */
    case clang::CK_ConstructorConversion: {
      exp_node content = subExpr->econtent;
      free_qual_type(resultType);
      free_location(subExpr->eloc);
      free(subExpr);
      return guard.setAssignResult(content, castExpr);
    }
    case clang::CK_Dynamic:
      return
        guard.setAssignResult(
          makeDynamicCastExpressionAux(
            _clangUtils->getBeginLoc(*castExpr), castExpr->getType(),
            castExpr->getSubExpr()->getType(), subExpr),
          castExpr);
    default:
      { std::cerr << "Unsupported context cast:";
#if CLANG_VERSION_MAJOR >= 11
        castExpr->dump(llvm::errs(), *_context);
#else
        castExpr->dump(llvm::errs(), _context->getSourceManager());
#endif
        std::cerr << "\nAborting\n";
        exit(2);
      };
  };
}

exp_node FramacVisitor::makeDynamicCastExpressionAux(
  const clang::SourceLocation loc,
  const clang::QualType result_type,
  const clang::QualType orig_type,
  expression subExpr)
{
  bool isReferenceType = result_type->isReferenceType();
  auto resultType = makeDefaultType(loc, result_type);
  init_expr init_arg =
    init_expr_Single_init(
      !isReferenceType ?
      subExpr:
      expression_cons(copy_loc(subExpr->eloc), exp_node_Address(subExpr)));
  const char* temp = mk_tmp_name();
  expression arg =
    expression_cons(
      copy_loc(subExpr->eloc),
      exp_node_Temporary(
        temp,
        qual_type_cons(
          NULL,
          typ_Pointer(
            pkind_PDataPointer(
              makeDefaultType(loc, orig_type->getPointeeType())))),
        init_arg, true));
  auto c_orig_type = makeDefaultType(loc,orig_type);
  auto orig_var =
    expression_cons(
      copy_loc(subExpr->eloc),
      exp_node_Variable(
        variable_Local(qualified_name_cons(NULL,strdup(temp)))));
  // auto orig_exp =
  //   isReferenceType?
  //   expression_cons(copy_loc(subExpr->eloc), exp_node_Dereference(orig_var)):
  //   orig_var;
  auto pvmt =
    _rttiTable.getPvmt(
      *_clangUtils,orig_type->getPointeeCXXRecordDecl(), orig_var);
  auto casted_exp =
    isReferenceType?
    expression_cons(copy_loc(subExpr->eloc), exp_node_Dereference(arg)) : arg;
  auto rpk_res =
    (isReferenceType?
     reference_or_pointer_kind_RPKDynamicReference:
     reference_or_pointer_kind_RPKDynamicPointer)
    (c_orig_type, pvmt);
  return exp_node_PointerCast(resultType, rpk_res, casted_exp);
}

exp_node FramacVisitor::makeDynamicCastExpression(
    const clang::CXXDynamicCastExpr* castExpr, bool* shouldDelay,
    /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard) {
  // expression subExpr =
  //   makeLocExpression(castExpr->getSubExpr(), shouldDelay, receiver);
  // qual_type resultType =
  //   makeDefaultType(castExpr->getExprLoc(), castExpr->getType());

  const clang::CXXRecordDecl* base = castExpr->getSubExpr()->getType()
      .getTypePtr()->getPointeeCXXRecordDecl();
  const clang::CXXRecordDecl* derived = castExpr->getType().getTypePtr()
      ->getPointeeCXXRecordDecl();
  if (!base)
    base = castExpr->getSubExpr()->getType().getTypePtr()
        ->getCanonicalTypeInternal().getTypePtr()->getAsCXXRecordDecl();
  if (!derived)
    derived = castExpr->getType().getTypePtr()
        ->getCanonicalTypeInternal().getTypePtr()->getAsCXXRecordDecl();
  if (base && derived) {
    if (hasInstanceContext()) {
      _tableForWaitingDeclarations.ensureGeneration(derived, unvisitedDecls());
      _tableForWaitingDeclarations.ensureGeneration(base, unvisitedDecls());
    }
    else if (shouldDelay && !*shouldDelay) {
      *shouldDelay = !_tableForWaitingDeclarations.hasVisited(derived)
          || !_tableForWaitingDeclarations.hasVisited(base);
    };
  };
  return
    guard.setAssignResult(
      makeDynamicCastExpressionAux(
        _clangUtils->getBeginLoc(*castExpr), castExpr->getType(),
        castExpr->getSubExpr()->getType(),
        makeLocExpression(castExpr->getSubExpr())),
      castExpr);
}

exp_node FramacVisitor::makeCompoundLiteralExpression(
    const clang::CompoundLiteralExpr* compoundExpr,
    bool* shouldDelay, /* statement */ list* receiver,
    bool hasImplicitThisStar, FramaCIRGenAction::ExpressionGuard& guard) {
  clang::QualType ctype = compoundExpr->getType();
  qual_type typ =
    makeDefaultType(compoundExpr->getExprLoc(), ctype);
  expression address = NULL;
  if (hasImplicitThisStar) {
    expression lval = guard.releaseExpr ();
    location loc = makeLocation(compoundExpr->getSourceRange());
    lval = getNodeReference(lval, compoundExpr->getType());
    address = expression_cons(loc,exp_node_Address(lval));
  };
  init_expr init =
    makeInitExpr(ctype, compoundExpr->getInitializer(), shouldDelay);
  const char* temp = mk_tmp_name();
  exp_node res = exp_node_Temporary(temp, typ, init, false);
  if (address) {
    location loc = makeLocation(compoundExpr->getSourceRange());
    res = exp_node_Assign(address, expression_cons(loc,res));
  };
  return res;
}

exp_node FramacVisitor::makeDeclRefExpression(
    const clang::DeclRefExpr* variableExpr, bool* shouldDelay,
    /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard) {
  variable result = NULL;
  clang::Decl::Kind kind = variableExpr->getDecl()->getKind();
  if (kind == clang::Decl::Field) {
    std::cerr << "Unsupported field access:";
#if CLANG_VERSION_MAJOR >= 11
    variableExpr->dump(llvm::errs(), *_context);
#else
    variableExpr->dump(llvm::errs(), _context->getSourceManager());
#endif
    std::cerr << "\nAborting\n";
    exit(2);
  }
  else if (kind >= clang::Decl::firstFunction
      && kind <= clang::Decl::lastFunction) {
    assert(llvm::dyn_cast<clang::FunctionDecl>(variableExpr->getDecl()));
    const clang::FunctionDecl* function
      = static_cast<const clang::FunctionDecl*>(variableExpr->getDecl());
    if (hasInstanceContext()) {
      if (!_tableForWaitingDeclarations.hasVisited(function)
            && function != _parents.getSFunctionDecl())
        unvisitedDecls().push_back(function);
      else {
        clang::Decl::Kind kindDecl = function->getDeclContext()->getDeclKind();
        if (kindDecl >= clang::Decl::firstRecord
            && kindDecl <= clang::Decl::lastRecord)
          _tableForWaitingDeclarations.ensureGeneration(
            static_cast<const clang::RecordDecl*>(function->getDeclContext()),
            unvisitedDecls());
      };
    }
    else if (shouldDelay && !*shouldDelay)
      *shouldDelay = !_tableForWaitingDeclarations.hasVisited(function)
            && function != _parents.getSFunctionDecl();
    tkind templateExtension = NULL;
    if (function->getTemplateSpecializationKind()
        >= clang::TSK_ImplicitInstantiation) {
      clang::FunctionTemplateSpecializationInfo* info
        = function->getTemplateSpecializationInfo();
      if (info)
        templateExtension =
          tkind_TTemplateInstance(_clangUtils->getTemplateExtension(info));
    };
    if (!templateExtension)
      templateExtension = tkind_TStandard();
    funkind fkind;
    if (kind == clang::Decl::CXXConstructor)
      fkind = funkind_FKConstructor(true);
    else if (kind == clang::Decl::CXXDestructor)
      fkind = funkind_FKDestructor(true);
    else if ((kind >= clang::Decl::firstCXXMethod)
             && (kind <= clang::Decl::lastCXXMethod)) {
      if (function->getCanonicalDecl()->getStorageClass() != clang::SC_Static)
        fkind = _clangUtils->cv_meth(static_cast<const clang::CXXMethodDecl*>(
          function));
      else
        fkind = funkind_FKFunction();
    }
    else
      fkind = funkind_FKFunction();
    signature sig = _clangUtils->makeSignature(*function);
    qualified_name qual = _clangUtils->makeQualifiedName(*function);
    if (fkind->tag_funkind == FKCONSTRUCTOR && strlen(qual->decl_name) == 0) {
      free(const_cast<char*>(qual->decl_name));
      qual->decl_name = strdup("constructor-special");
    };
    result = variable_CodePointer(qual, sig, fkind, 
      function->isInExternCContext(), templateExtension);
  }
  else if (kind == clang::Decl::Var) {
    assert(llvm::dyn_cast<clang::VarDecl>(variableExpr->getDecl()));
    const clang::VarDecl* var
        = static_cast<const clang::VarDecl*>(variableExpr->getDecl());
    if (var->hasLocalStorage())
      result = variable_Local(_clangUtils->makeQualifiedName(*var));
    else { // var->hasGlobalStorage()
      result = variable_Global(_clangUtils->makeQualifiedName(*var));
      if (shouldDelay && !*shouldDelay) {
        *shouldDelay = !_tableForWaitingDeclarations.hasVisited(var);
      };
    }
  }
  else if (kind == clang::Decl::ImplicitParam)
    result = variable_FunctionParameter(strdup(variableExpr
        ->getDecl()->getName().str().c_str()));
  else if (kind == clang::Decl::ParmVar)
    result = variable_FunctionParameter(strdup(variableExpr
        ->getDecl()->getName().str().c_str()));
  else if (kind == clang::Decl::EnumConstant) {
    assert(llvm::dyn_cast<clang::EnumConstantDecl>(variableExpr->getDecl()));
    const clang::EnumConstantDecl* enumDecl
      = static_cast<const clang::EnumConstantDecl*>(variableExpr->getDecl());
    const clang::QualType t = enumDecl->getType();
    assert (llvm::dyn_cast<clang::EnumType const>(t));
    const clang::EnumType* enumType =
      static_cast<const clang::EnumType*>(t.getTypePtr());
    const clang::EnumDecl* declEnum = enumType->getDecl();
    if (hasInstanceContext()) {
      if (!_tableForWaitingDeclarations.hasVisited(declEnum))
        unvisitedDecls().push_back(declEnum);
      else {
        clang::Decl::Kind kindDecl = declEnum->getDeclContext()->getDeclKind();
        if (kindDecl >= clang::Decl::firstRecord
            && kindDecl <= clang::Decl::lastRecord)
          _tableForWaitingDeclarations.ensureGeneration(
            static_cast<const clang::RecordDecl*>(declEnum->getDeclContext()),
            unvisitedDecls());
      };
    }
    else if (shouldDelay && !*shouldDelay)
      *shouldDelay = !_tableForWaitingDeclarations.hasVisited(
          enumType->getDecl());
    return
      guard.setAssignResult(
        exp_node_Constant(
          compilation_constant_EnumCst(
            _clangUtils->makeQualifiedName(*variableExpr->getDecl()),
            ekind_cons(
              _clangUtils->makeQualifiedName(*declEnum),
              Clang_utils::isExternCContext(enumType->getDecl())),
            (int64_t)enumDecl->getInitVal().getLimitedValue(UINT64_MAX))),
        variableExpr);
  }
  else if (kind == clang::Decl::IndirectField) {
    std::cerr << "Unsupported indirect field:";
#if CLANG_VERSION_MAJOR >= 11
    variableExpr->dump(llvm::errs(), *_context);
#else
    variableExpr->dump(llvm::errs(), _context->getSourceManager());
#endif
    std::cerr << "\nAborting\n";
    exit(2);
  }
  else {
    std::cerr << "Unsupported reference expression:";
#if CLANG_VERSION_MAJOR >= 11
    variableExpr->dump(llvm::errs(), *_context);
#else
    variableExpr->dump(llvm::errs(), _context->getSourceManager());
#endif
    std::cerr << "\nAborting\n";
    exit(2);
  };
  exp_node eres = exp_node_Variable(result);
  if (_clangUtils->lvalHasRefType(variableExpr)) {
    location loc = makeLocation(variableExpr->getSourceRange());
    expression exp_res = expression_cons(loc,eres);
    eres = exp_node_Unary_operator(uokind_UOCastDeref(),exp_res);
  }
  return guard.setAssignResult(eres, variableExpr);
}

exp_node FramacVisitor::makeMaterializeTemporaryExpression(
    const clang::MaterializeTemporaryExpr* tmpExpr, bool* shouldDelay,
    /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard) {
  expression oldThisStar = _implicitThisStar;
  location loc = makeLocation(tmpExpr->getSourceRange());
  const char* tmp = mk_materialized_tmp_name();
  qualified_name qtmp = qualified_name_cons(NULL,tmp);
  expression etmp =
    expression_cons(loc, exp_node_Variable(variable_Local(qtmp)));
  _implicitThisStar = etmp;
  const clang::Expr* e =
#if CLANG_VERSION_MAJOR >= 10
    tmpExpr->getSubExpr();
#else
    tmpExpr->GetTemporaryExpr();
#endif
  init_expr temp = makeInitExpr(tmpExpr->getType(), e, shouldDelay);
  qual_type temp_type =
    makeDefaultType(tmpExpr->getExprLoc(), tmpExpr->getType());
  _implicitThisStar = oldThisStar;
  return guard.setAssignResult(exp_node_Temporary(tmp,temp_type,temp,false),
                               tmpExpr);
}

exp_node
FramacVisitor::makeBindTemporaryExpression(
    const clang::CXXBindTemporaryExpr* tmp, bool* shouldDelay,
    /* statement */ list* receiver, bool hasImplicitThisStar,
    FramaCIRGenAction::ExpressionGuard& guard) {
  expression oldThisStar = _implicitThisStar;
  location loc = makeLocation(tmp->getSourceRange());
  // location locCopy = copy_loc(loc);
  const char* tmp_name = NULL;
  expression etmp = NULL;
  if (hasImplicitThisStar) {
    etmp = guard.releaseExpr();
  } else {
    tmp_name = mk_tmp_name();
    qualified_name qtmp = qualified_name_cons(NULL,tmp_name);
    etmp =
      expression_cons(
        loc, exp_node_Variable(variable_Local(qtmp)));
  }
  _implicitThisStar = etmp;
  // expression addr = expression_cons(locCopy,
  //     exp_node_Address(expression_dup(etmp)));
  init_expr temp = makeInitExpr(tmp->getType(),tmp->getSubExpr(), shouldDelay);
  qual_type temp_type = makeDefaultType(tmp->getExprLoc(), tmp->getType());
  _implicitThisStar = oldThisStar;
  if (tmp_name)
    return guard.setAssignResult(
        exp_node_Temporary(tmp_name,temp_type,temp, false),tmp);
  else if (temp->tag_init_expr == SINGLE_INIT)
    return
      guard.setAssignResult(
        temp->cons_init_expr.Single_init.definition->econtent,tmp);
  else {
    tmp_name = mk_tmp_name();
    return guard.setAssignResult(
        exp_node_Temporary(tmp_name,temp_type,temp,false),tmp);
  }
}

exp_node FramacVisitor::makeUnaryOperator(
    const clang::UnaryOperator* unaryExpr, bool* shouldDelay,
    /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard) {
  uokind unaryKind = NULL;
  // assign_kind assignment = AKRVALUE;
  switch (unaryExpr->getOpcode()) {
    case clang::UO_PostInc:
      unaryKind = uokind_UOPostInc(); /* assignment = AKASSIGN; */
      break;
    case clang::UO_PostDec:
      unaryKind = uokind_UOPostDec(); /* assignment = AKASSIGN; */
      break;
    case clang::UO_PreInc:
      unaryKind = uokind_UOPreInc(); /* assignment = AKASSIGN; */
      break;
    case clang::UO_PreDec:
      unaryKind = uokind_UOPreDec(); /* assignment = AKASSIGN; */
      break;
    case clang::UO_AddrOf:
      { expression esubexpr = 
          makeLocExpression(unaryExpr->getSubExpr(),shouldDelay,receiver);
        return guard.setAssignResult(exp_node_Address(esubexpr), unaryExpr);
      };
    case clang::UO_Deref:
      { exp_node subexpr = makeExpression(unaryExpr->getSubExpr(),
                                          shouldDelay,receiver);
        expression esubexpr = expression_cons(makeLocation(
              unaryExpr->getSubExpr()->getSourceRange()), subexpr);
        return guard.setAssignResult( exp_node_Dereference(esubexpr),unaryExpr);
      };
    case clang::UO_Plus:
      return guard.setAssignResult(makeExpression(unaryExpr->getSubExpr(),
          shouldDelay,receiver), unaryExpr);
    case clang::UO_Minus:
      unaryKind = uokind_UOOpposite(); /* assignment = AKRVALUE; */
      break;
    case clang::UO_Not:
      unaryKind = uokind_UOBitNegate(); /* assignment = AKRVALUE; */
      break;
    case clang::UO_LNot:
      unaryKind = uokind_UOLogicalNegate(); /* assignment = AKRVALUE; */
      break;
    case clang::UO_Extension:
      return guard.setAssignResult(makeExpression(unaryExpr->getSubExpr(),
        shouldDelay, receiver), unaryExpr);
    default:
      std::cerr << "Unsupported unary expressions:";
#if CLANG_VERSION_MAJOR >= 11
      unaryExpr->dump(llvm::errs(), *_context);
#else
      unaryExpr->dump(llvm::errs(), _context->getSourceManager());
#endif
      std::cerr << "\nAborting\n";
      exit(2);
  };
  exp_node subexpr = makeExpression(unaryExpr->getSubExpr(), shouldDelay,
      receiver);
  expression esubexpr = expression_cons(makeLocation(
      unaryExpr->getSubExpr()->getSourceRange()), subexpr);
  return guard.setAssignResult( exp_node_Unary_operator(unaryKind,
      /* assignment, */ esubexpr), unaryExpr);
}

exp_node
FramacVisitor::makeConstantArrayInitExpression(
    const clang::ConstantArrayType& arrayType, const clang::Expr* expr,
    expression lvalueThisStar, bool* shouldDelay,
    /* statement */ list* receiver) {
  const llvm::APInt& size = arrayType.getSize();
  ForwardReferenceList forwardStmts(*receiver);
  clang::SourceLocation sloc = expr->getExprLoc();
  qual_type typ = makeDefaultType(sloc, arrayType.getElementType());
  location defaultLoc = makeLocation(sloc);

  const char* temp = mk_tmp_name();
  forwardStmts.insertContainer(statement_VarDecl(
    defaultLoc, temp, qual_type_cons(NULL,
      typ_Pointer(pkind_PDataPointer(typ))),
    opt_some_container(init_expr_Single_init(lvalueThisStar))));

  clang::ImplicitValueInitExpr subExpr(arrayType.getElementType());
  /* statement */ list elementResult = NULL;
  _implicitThisStar = expression_cons(copy_loc(defaultLoc),
    exp_node_Dereference(expression_cons(copy_loc(defaultLoc),
      exp_node_Binary_operator(BOPLUS, AKRVALUE,
        expression_cons(copy_loc(defaultLoc), exp_node_Variable(
          variable_Local(qualified_name_cons(NULL, strdup(temp))))),
        expression_cons(copy_loc(defaultLoc), exp_node_Variable(
          variable_Local(qualified_name_cons(NULL,
                strdup("_frama_c_index")))))))));
  exp_node init_res = makeExpression(&subExpr, shouldDelay, &elementResult);
  if (init_res) {
    ForwardReferenceList subForwardStmts(elementResult);
    statement initPart = statement_Expression(
      copy_loc(defaultLoc), expression_cons(copy_loc(defaultLoc),
        _implicitThisStar
          ? exp_node_Assign(_implicitThisStar, expression_cons(
                copy_loc(defaultLoc), init_res))
          : init_res));
    subForwardStmts.insertContainer(initPart);
  }
  else if (_implicitThisStar) {
    free_expression(_implicitThisStar);
    _implicitThisStar = NULL;
  };
  forwardStmts.insertContainer(
    statement_For(
      copy_loc(defaultLoc),
      init_statement_IVarDecl(
        cons_container(
          init_declarator_cons(
            strdup("_frama_c_index"),
            qual_type_cons(NULL, typ_Int(IINT)),
            opt_some_container(
              init_expr_Single_init(makeIntLiteral(defaultLoc,IINT,0)))),
          NULL)),
      opt_some_container(
        expression_cons(
          copy_loc(defaultLoc),
          exp_node_Binary_operator(
            BOLESS, AKRVALUE,
            expression_cons(
              copy_loc(defaultLoc),
              exp_node_Variable(
                variable_Local(
                  qualified_name_cons(NULL, strdup("_frama_c_index"))))),
            makeIntLiteral(
              defaultLoc,IINT, (int64_t) size.getLimitedValue(UINT64_MAX))))),
      incr_statement_CExpression(
        expression_cons(
          copy_loc(defaultLoc),
          exp_node_Unary_operator(
            uokind_UOPostInc(),
            expression_cons(
              copy_loc(defaultLoc),
              exp_node_Variable(
                variable_Local(
                  qualified_name_cons(NULL, strdup("_frama_c_index")))))))),
      statement_Block(copy_loc(defaultLoc), elementResult),
      NULL /* annot = should unroll the loop */));
  return exp_node_Dereference(expression_cons(copy_loc(defaultLoc),
    exp_node_Variable(variable_Local(qualified_name_cons(NULL,
      strdup(temp))))));
}
  
exp_node FramacVisitor::makeRecordInitExpression(
  const clang::RecordDecl& record,
  const clang::Expr* expr, expression lvalueThisStar,
  bool* shouldDelay, /* statement */ list* receiver) {
  const clang::CXXRecordDecl* cxxRecord
      = llvm::dyn_cast<clang::CXXRecordDecl>(&record);
  if (cxxRecord && cxxRecord->hasDefaultConstructor()) {
    // const char* temp = mk_tmp_name();
    location defaultLoc = makeLocation(expr->getSourceRange());
    expression tmpvar = expression_cons(defaultLoc,
        exp_node_Address(lvalueThisStar));
    qualified_name name = _clangUtils->makeQualifiedName(record);
    // qualified_name recordName = qualified_name_dup(name);
    /* qualification */ list* endQual = &name->prequalification;
    while (*endQual) endQual = &(*endQual)->next;
    const clang::ClassTemplateSpecializationDecl* TSD
      = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(cxxRecord);
    if (TSD)
      *endQual =
        cons_container(
          qualification_QTemplateInstance(
            name->decl_name, _clangUtils->getTemplateExtension(TSD)),
          NULL);
    else
      *endQual = cons_container(qualification_QStructOrClass(
          name->decl_name), NULL);
    name->decl_name = strdup("constructor-special");
    signature sig =
      signature_cons(qual_type_cons(NULL, typ_Void()), NULL, false);
    return exp_node_Static_call(
      name, sig, funkind_FKConstructor(true),
      cons_container(tmpvar, NULL),
      tkind_TStandard(),
      false /* extern_c_call */);
  }
  else {
    qual_type typ = makeDefaultType(expr->getExprLoc(), expr->getType());
    location defaultLoc = makeLocation(expr->getSourceRange());
    const char* temp = mk_tmp_name();
    ForwardReferenceList forwardStmts(*receiver);
    forwardStmts.insertContainer(statement_VarDecl(defaultLoc, temp,
      qual_type_cons(NULL, typ_Pointer(pkind_PDataPointer(typ))),
      opt_some_container(init_expr_Single_init(expression_cons(
        copy_loc(defaultLoc), exp_node_Address(lvalueThisStar))))));

    if (hasInstanceContext()) {
      _tableForWaitingDeclarations.ensureGeneration(&record, unvisitedDecls());
    }
    else if (shouldDelay && !*shouldDelay)
      *shouldDelay = !_tableForWaitingDeclarations.hasVisited(&record);
    clang::RecordDecl::field_iterator fieldIterEnd = record.field_end();
    for (clang::RecordDecl::field_iterator fieldIter
        = record.field_begin(); fieldIter != fieldIterEnd; ++fieldIter) {
      clang::ImplicitValueInitExpr subExpr(fieldIter->getType());
      _implicitThisStar = expression_cons(copy_loc(defaultLoc),
          exp_node_FieldAccess(expression_cons(copy_loc(defaultLoc),
            exp_node_Dereference(expression_cons(copy_loc(defaultLoc),
                exp_node_Variable(variable_Local(qualified_name_cons(
                  NULL, strdup(temp))))))),
            copy_string(fieldIter->getNameAsString())));
      if(fieldIter->getType()->isReferenceType())
        _implicitThisStar =
          expression_cons(
            copy_loc(defaultLoc),
            exp_node_Unary_operator(uokind_UOCastDeref(),_implicitThisStar));
      exp_node init_res = makeExpression(&subExpr, shouldDelay, receiver);
      if (init_res) {
        statement initPart = statement_Expression(copy_loc(
          defaultLoc), expression_cons(copy_loc(defaultLoc),
            _implicitThisStar ? exp_node_Assign(_implicitThisStar,
                expression_cons(copy_loc(defaultLoc), init_res))
                          : init_res));
        forwardStmts.insertContainer(initPart);
      }
      else if (_implicitThisStar) {
        free_expression(_implicitThisStar);
        _implicitThisStar = NULL;
      };
    };
    return exp_node_Dereference(expression_cons(copy_loc(
      defaultLoc), exp_node_Variable(variable_Local(
        qualified_name_cons(NULL, strdup(temp))))));
  };
}

exp_node
FramacVisitor::makeImplicitValueInitExpression(
    const clang::ImplicitValueInitExpr* expr, bool* shouldDelay,
    /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard,
    const clang::Type* type)
{ if (!type)
    type = expr->getType().getTypePtr();
  clang::Type::TypeClass typeClass=type->getTypeClass();
  if ((typeClass >= clang::Type::ConstantArray
        && typeClass <= clang::Type::DependentSizedArray)
      || typeClass == clang::Type::Record) {
    if (!receiver) {
      std::cerr << "Unsupported initialization:";
#if CLANG_VERSION_MAJOR >= 11
      expr->dump(llvm::errs(), *_context);
#else
      expr->dump(llvm::errs(), _context->getSourceManager());
#endif
      std::cerr << "\nAborting\n";
      exit(2);
    };
    expression lvalueThisStar = guard.releaseExpr();
    if (expr->getStmtClass() == clang::Stmt::InitListExprClass) {
      qual_type typ = makeDefaultType(expr->getExprLoc(), expr->getType());
      location loc = makeLocation(expr->getSourceRange());
      init_expr init = makeInitExpr(expr->getType(),expr);
      const char* temp = mk_tmp_name();
      exp_node res = exp_node_Temporary(temp, typ, init, false);
      return exp_node_Assign(lvalueThisStar,expression_cons(copy_loc(loc),res));
    }
    else if (expr->getStmtClass() == clang::Stmt::ImplicitValueInitExprClass) {
      if (typeClass == clang::Type::ConstantArray)
        return makeConstantArrayInitExpression((const clang::ConstantArrayType&)
            *type, expr, lvalueThisStar, shouldDelay, receiver);
      else if (typeClass == clang::Type::Record)
        return makeRecordInitExpression(*((const clang::RecordType&)
            *type).getDecl(), expr, lvalueThisStar, shouldDelay, receiver);
      else {
        // dynamic array => generate a loop like ConstantArray
      };
    }
    std::cerr << "Unsupported initialization:";
#if CLANG_VERSION_MAJOR >= 11
    expr->dump(llvm::errs(), *_context);
#else
    expr->dump(llvm::errs(), _context->getSourceManager());
#endif
    std::cerr << "\nAborting\n";
    exit(2);
  };
  switch (typeClass) {
    case clang::Type::Pointer: case clang::Type::MemberPointer:
      return guard.setAssignResult(
        exp_node_PointerCast(
          makeDefaultType(expr->getExprLoc(), expr->getType()),
          reference_or_pointer_kind_RPKPointer(),
          makeIntLiteral(makeLocation(expr->getSourceRange()),IINT,0)),
        expr);
    case clang::Type::Builtin:
      { auto builtinType = llvm::dyn_cast<const clang::BuiltinType>(type);
        assert(builtinType);
          //integral init is handled somewhere else
          if (!type->isIntegerType()) { 
            if (type->isRealFloatingType()) {
              location loc = _clangUtils->makeExprLocation(*expr);
              fkind k = _clangUtils->makeFloatConstantType(type);
              expression res = makeFloatZero(loc, k);
              free_location(loc);
              return guard.setAssignResult(res, expr);
            }
            if (builtinType->getKind() == clang::BuiltinType::NullPtr) {
              return guard.setAssignResult(
                exp_node_PointerCast(
                  qual_type_cons(
                    NULL,
                    typ_Pointer(
                      pkind_PDataPointer(qual_type_cons(NULL, typ_Void())))),
                  reference_or_pointer_kind_RPKPointer(),
                  makeIntLiteral(makeLocation(expr->getSourceRange()),IINT,0)),
                expr);
            }
            std::cerr
              << "Unsupported Builtin-type: "
              << builtinType->getName(_context->getPrintingPolicy()).str()
              << "\nAborting\n";
            //TODO: raise exception and try to continue with rest of file.
            exit(2);
          };
      };
      break;
    case clang::Type::Paren:
      assert(llvm::dyn_cast<const clang::ParenType>(type));
      return makeImplicitValueInitExpression(expr, shouldDelay, receiver, guard,
        static_cast<const clang::ParenType*>(type)->desugar().getTypePtr());
    case clang::Type::UnresolvedUsing:
      assert(llvm::dyn_cast<const clang::UnresolvedUsingType>(type));
      return makeImplicitValueInitExpression(expr, shouldDelay, receiver, guard,
        static_cast<const clang::UnresolvedUsingType*>(type)->desugar()
          .getTypePtr());
    case clang::Type::LValueReference:
    case clang::Type::RValueReference:
    case clang::Type::FunctionNoProto:
    case clang::Type::FunctionProto:
      std::cerr << "Unsupported default initialization with reference type \""
          << expr->getType().getAsString () << "\"\nAborting\n";
      exit(2);
    case clang::Type::SubstTemplateTypeParm:
      { assert(llvm::dyn_cast<const clang::SubstTemplateTypeParmType>(type));
        return makeImplicitValueInitExpression(expr, shouldDelay, receiver,
          guard, static_cast<const clang::SubstTemplateTypeParmType*>(type)
            ->getReplacementType().getTypePtr());
      };
    case clang::Type::Typedef:
      assert(llvm::dyn_cast<const clang::TypedefType>(type));
      return makeImplicitValueInitExpression(expr, shouldDelay, receiver, guard,
        static_cast<const clang::TypedefType*>(type)->desugar().getTypePtr());
    case clang::Type::Elaborated:
      assert(llvm::dyn_cast<const clang::ElaboratedType>(type));
      return makeImplicitValueInitExpression(expr, shouldDelay, receiver, guard,
        static_cast<const clang::ElaboratedType*>(type)->desugar()
          .getTypePtr());
    default:
      break;
  };
  ikind kind = _clangUtils->makeIntConstantType(type);
  return 
    guard.setAssignResult(
      exp_node_Constant(
        compilation_constant_IntCst(kind, ICLITERAL,0)),expr);
}

exp_node FramacVisitor::makeUnaryExprOrTypeTraitExpression(
    const clang::UnaryExprOrTypeTraitExpr* expr, bool* shouldDelay,
    /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard)
{ tcckind kind;
  if (expr->getKind() == clang::UETT_SizeOf)
    kind = TCCSIZEOF;
  else if (expr->getKind() == clang::UETT_AlignOf)
    kind = TCCALIGNOF;
  else {
    std::cerr << "Unsupported expression:";
#if CLANG_VERSION_MAJOR >= 11
    expr->dump(llvm::errs(), *_context);
#else
    expr->dump(llvm::errs(), _context->getSourceManager());
#endif
    std::cerr << "\nAborting\n";
    exit(2);
  };
  typ typeArgument;
  if (hasInstanceContext()) {
    FramaCIRGenAction::UnvisitedRegistration
      unvisitedRegistration(*this);
    typeArgument =
      _clangUtils->makePlainType(
        expr->getExprLoc(), expr->getTypeOfArgument(), &unvisitedRegistration);
  }
  else
    typeArgument =
      _clangUtils->makePlainType(expr->getExprLoc(), expr->getTypeOfArgument());
  return 
    guard.setAssignResult(
      exp_node_Constant(compilation_constant_TypeCst(kind, typeArgument)), expr);
}

exp_node FramacVisitor::makeAtomicExprExpression(
    const clang::AtomicExpr* sexpr, bool* shouldDelay,
    /* statement */ list* receiver, FramaCIRGenAction::ExpressionGuard& guard) {
  list /* expression */ arguments = NULL;
  clang::AtomicExpr* expr = const_cast<clang::AtomicExpr*>(sexpr);
  ForwardReferenceList forwardArguments(arguments);
  int childNumber = expr->getNumSubExprs();
  list /* qual_type */ parameters = NULL;
  ForwardReferenceList forwardParameters(parameters);
  for (int child = 0; child < childNumber; ++child) {
    clang::Expr const* childExpr = expr->getSubExprs()[child];
    expression argument = makeLocExpression(childExpr, shouldDelay, receiver);
    forwardArguments.insertContainer(argument);
    FramaCIRGenAction::UnvisitedRegistration
      unvisitedRegistration(*this);
    forwardParameters.insertContainer(
      _clangUtils->makeType(
        childExpr->getExprLoc(),childExpr->getType(), &unvisitedRegistration));
  }

  const char* name = NULL;
  switch (expr->getOp()) {
#define BUILTIN(ID, TYPE, ATTRS)
#define ATOMIC_BUILTIN(ID, TYPE, ATTRS)                 \
    case clang::AtomicExpr::AO ## ID: name = #ID; break;
#include "clang/Basic/Builtins.def"
    default:
      break;
  };
  qualified_name callName = qualified_name_cons(NULL, strdup(name));
  signature sig = signature_cons(qual_type_cons(NULL, typ_Void()),
    parameters, false);
  return exp_node_Static_call(callName, sig, funkind_FKFunction(), arguments,
      tkind_TStandard(), true /* isExternC */);
}

exp_node FramacVisitor::makeExpression(
  const clang::Expr* expr, bool* shouldDelay, /* statement */ list* receiver) {
  bool hasImplicitThisStar = _implicitThisStar != NULL;
  bool isImplicitThisBare = _isImplicitThisBare;
  _isImplicitThisBare = false;
  FramaCIRGenAction::ExpressionGuard guard(*this, _implicitThisStar);

  switch (expr->getStmtClass()) {
    case clang::Stmt::ArraySubscriptExprClass:
      { assert(llvm::dyn_cast<clang::ArraySubscriptExpr>(expr));
        const clang::ArraySubscriptExpr* array
            = static_cast<const clang::ArraySubscriptExpr*>(expr);
        expression base = makeLocExpression(array->getBase(), shouldDelay);
        expression index = makeLocExpression(array->getIdx(), shouldDelay);
        return guard.setAssignResult(exp_node_ArrayAccess(base, index), expr);
      }
    case clang::Stmt::BinaryOperatorClass:
    case clang::Stmt::CompoundAssignOperatorClass:
      { assert(llvm::dyn_cast<clang::BinaryOperator>(expr));
        const clang::BinaryOperator* binaryOperator
          = static_cast<const clang::BinaryOperator*>(expr);
        bokind type = BOPLUS;
        assign_kind assignment = AKRVALUE;
        switch (binaryOperator->getOpcode()) {
          case clang::BO_PtrMemD:
          case clang::BO_PtrMemI:
            return makeExpression(binaryOperator->getRHS(), shouldDelay);
          case clang::BO_Mul:
            type = BOTIMES; assignment = AKRVALUE; break;
          case clang::BO_Div:
            type = BODIVIDE; assignment = AKRVALUE; break;
          case clang::BO_Rem:
            type = BOMODULO; assignment = AKRVALUE; break;
          case clang::BO_Add:
            type = BOPLUS; assignment = AKRVALUE; break;
          case clang::BO_Sub:
            type = BOMINUS; assignment = AKRVALUE; break;
          case clang::BO_Shl:
            type = BOLEFTSHIFT; assignment = AKRVALUE; break;
          case clang::BO_Shr:
            type = BORIGHTSHIFT; assignment = AKRVALUE; break;
          case clang::BO_LT:
            type = BOLESS; assignment = AKRVALUE; break;
          case clang::BO_GT:
            type = BOGREATER; assignment = AKRVALUE; break;
          case clang::BO_LE:
            type = BOLESSOREQUAL; assignment = AKRVALUE; break;
          case clang::BO_GE:
            type = BOGREATEROREQUAL; assignment = AKRVALUE; break;
          case clang::BO_EQ:
            type = BOEQUAL; assignment = AKRVALUE; break;
          case clang::BO_NE:
            type = BODIFFERENT; assignment = AKRVALUE; break;
          case clang::BO_And:
            type = BOBITAND; assignment = AKRVALUE; break;
          case clang::BO_Xor:
            type = BOBITEXCLUSIVEOR; assignment = AKRVALUE; break;
          case clang::BO_Or:
            type = BOBITOR; assignment = AKRVALUE; break;
          case clang::BO_LAnd:
            type = BOLOGICALAND; assignment = AKRVALUE; break;
          case clang::BO_LOr:
            type = BOLOGICALOR; assignment = AKRVALUE; break;
          case clang::BO_Assign:
            { exp_node lhsPart = makeExpression(binaryOperator->getLHS(),
                                                shouldDelay,receiver);
              expression elhsPart = expression_cons(makeLocation(
                    binaryOperator->getLHS()->getSourceRange()), lhsPart);
              exp_node rhsPart = makeExpression(binaryOperator->getRHS(),
                                                shouldDelay,receiver);
              expression erhsPart = expression_cons(makeLocation(
                    binaryOperator->getRHS()->getSourceRange()), rhsPart);
              return guard.setAssignResult(exp_node_Assign(elhsPart, erhsPart),
                  expr);
            };
          case clang::BO_MulAssign:
            type = BOTIMES; assignment = AKASSIGN; break;
          case clang::BO_DivAssign:
            type = BODIVIDE; assignment = AKASSIGN; break;
          case clang::BO_RemAssign:
            type = BOMODULO; assignment = AKASSIGN; break;
          case clang::BO_AddAssign:
            type = BOPLUS; assignment = AKASSIGN; break;
          case clang::BO_SubAssign:
            type = BOMINUS; assignment = AKASSIGN; break;
          case clang::BO_ShlAssign:
            type = BOLEFTSHIFT; assignment = AKASSIGN; break;
          case clang::BO_ShrAssign:
            type = BORIGHTSHIFT; assignment = AKASSIGN; break;
          case clang::BO_AndAssign:
            type = BOBITAND; assignment = AKASSIGN; break;
          case clang::BO_XorAssign:
            type = BOBITEXCLUSIVEOR; assignment = AKASSIGN; break;
          case clang::BO_OrAssign:
            type = BOBITOR; assignment = AKASSIGN; break;
          case clang::BO_Comma:
            type = BOCOMMA; assignment = AKRVALUE; break;
          case clang::BO_Cmp: // does not seem to be fully supported by clang
            //itself according to https://clang.llvm.org/cxx_status.html#cxx2a
          std::cerr << "Unsupported spaceship (<=>) operator:";
#if CLANG_VERSION_MAJOR >= 11
          expr->dump(llvm::errs(), *_context);
#else
          expr->dump(llvm::errs(), _context->getSourceManager());
#endif
          std::cerr << "\nAborting\n";
          exit(2);
          default:
            std::cerr << "Unsupported binary expression:";
#if CLANG_VERSION_MAJOR >= 11
            expr->dump(llvm::errs(), *_context);
#else
            expr->dump(llvm::errs(), _context->getSourceManager());
#endif
            std::cerr << "\nAborting\n";
            exit(2);
        };
        exp_node lhsPart = makeExpression(binaryOperator->getLHS(),
                                          shouldDelay,receiver);
        expression elhsPart = expression_cons(makeLocation(
              binaryOperator->getLHS()->getSourceRange()), lhsPart);
        exp_node rhsPart = makeExpression(binaryOperator->getRHS(),
                                          shouldDelay,receiver);
        expression erhsPart = expression_cons(makeLocation(
              binaryOperator->getRHS()->getSourceRange()), rhsPart);
        return guard.setAssignResult(exp_node_Binary_operator(type, assignment,
              elhsPart, erhsPart), expr);
      }
    case clang::Stmt::ConditionalOperatorClass:
      { assert(llvm::dyn_cast<clang::ConditionalOperator>(expr));
        const clang::ConditionalOperator* ternaryOperator
            = static_cast<const clang::ConditionalOperator*>(expr);
        exp_node condition = makeExpression(ternaryOperator->getCond(),
                                            shouldDelay,receiver);
        expression econdition = expression_cons(makeLocation(
              ternaryOperator->getCond()->getSourceRange()), condition);
        exp_node truePart = makeExpression(ternaryOperator->getTrueExpr(),
                                           shouldDelay,receiver);
        expression etruePart = expression_cons(makeLocation(
              ternaryOperator->getTrueExpr()->getSourceRange()), truePart);
        exp_node falsePart = makeExpression(ternaryOperator->getFalseExpr(),
                                            shouldDelay,receiver);
        expression efalsePart = expression_cons(makeLocation(
              ternaryOperator->getFalseExpr()->getSourceRange()), falsePart);
        return guard.setAssignResult(exp_node_Conditional(econdition,
              etruePart, efalsePart), expr);
      }
    case clang::Stmt::CXXBoolLiteralExprClass:
      { bool val = (static_cast<const clang::CXXBoolLiteralExpr*>(expr))
            ->getValue();
        compilation_constant cst =
          compilation_constant_IntCst(IBOOL, ICLITERAL, (int64_t)val);
        return guard.setAssignResult(exp_node_Constant(cst), expr);
      }
    case clang::Stmt::CXXTemporaryObjectExprClass:
      return makeTemporaryObjectExpression(
          static_cast<const clang::CXXTemporaryObjectExpr*>(expr),
          shouldDelay, receiver);
    case clang::Stmt::CXXConstructExprClass: {
      const auto constructor_expr =
        llvm::dyn_cast<clang::CXXConstructExpr>(expr);
      return makeConstructExpression(
        constructor_expr,
        shouldDelay, receiver, hasImplicitThisStar, isImplicitThisBare, guard);
    }
    case clang::Stmt::CXXDefaultArgExprClass:
      { assert(llvm::dyn_cast<clang::CXXDefaultArgExpr>(expr));
        const clang::CXXDefaultArgExpr* defaultArg
            = static_cast<const clang::CXXDefaultArgExpr*>(expr);
        return guard.setAssignResult(makeExpression(defaultArg->getExpr(),
          shouldDelay,receiver), expr);
      };
    case clang::Stmt::CXXDeleteExprClass:
      assert(llvm::dyn_cast<clang::CXXDeleteExpr>(expr));
      return guard.setAssignResult(makeDeleteExpression(
          static_cast<const clang::CXXDeleteExpr*>(expr),
          shouldDelay,receiver), expr);
    case clang::Stmt::CXXNewExprClass:
      assert(llvm::dyn_cast<clang::CXXNewExpr>(expr));
      return 
        guard.setAssignResult(
          makeNewExpression(
            static_cast<const clang::CXXNewExpr*>(expr), shouldDelay,receiver),
          expr);
    case clang::Stmt::GNUNullExprClass:
    case clang::Stmt::CXXNullPtrLiteralExprClass:
      { compilation_constant cst =
          compilation_constant_IntCst(IINT, ICLITERAL, 0);
        return guard.setAssignResult(exp_node_Constant(cst), expr);
      }
    case clang::Stmt::CXXThisExprClass:
      { variable thisVariable = variable_FunctionParameter("this");
        return guard.setAssignResult(exp_node_Variable(thisVariable), expr);
      }
    case clang::Stmt::CXXThrowExprClass:
      assert(llvm::dyn_cast<clang::CXXThrowExpr>(expr));
      { const clang::Expr* subExpr = static_cast<const clang::CXXThrowExpr*>
          (expr)->getSubExpr();
        return guard.setAssignResult(exp_node_Throw(subExpr
          ? opt_some_container(expression_cons(
              makeLocation(subExpr->getSourceRange()),
              makeExpression(subExpr, shouldDelay, receiver)))
          : opt_none()), expr);
      };
    case clang::Stmt::CXXTypeidExprClass:
      std::cerr << "Unsupported typeid:";
#if CLANG_VERSION_MAJOR >= 11
      expr->dump(llvm::errs(), *_context);
#else
      expr->dump(llvm::errs(), _context->getSourceManager());
#endif
      std::cerr << "\nAborting\n";
      exit(2);
    case clang::Stmt::CallExprClass:
    case clang::Stmt::CXXOperatorCallExprClass:
      assert(llvm::dyn_cast<clang::CallExpr>(expr));
      return makeCallExpression(static_cast<const clang::CallExpr*>(expr),
          shouldDelay, receiver, guard);
    case clang::Stmt::CXXMemberCallExprClass:
      assert(llvm::dyn_cast<clang::CXXMemberCallExpr>(expr));
      return makeMemberCallExpression(
          static_cast<const clang::CXXMemberCallExpr*>(expr),
          shouldDelay, receiver, guard);
    case clang::Stmt::CStyleCastExprClass:
    case clang::Stmt::CXXFunctionalCastExprClass:
    case clang::Stmt::CXXStaticCastExprClass:
    case clang::Stmt::CXXReinterpretCastExprClass:
    case clang::Stmt::CXXConstCastExprClass:
    case clang::Stmt::ImplicitCastExprClass:
      // TODO: Do not generate cast when clang make it a noop
      assert(llvm::dyn_cast<clang::CastExpr>(expr));
      return makeCastExpression(
          static_cast<const clang::CastExpr*>(expr),
          shouldDelay, receiver, guard);
    case clang::Stmt::CXXDynamicCastExprClass:
      assert(llvm::dyn_cast<clang::CXXDynamicCastExpr>(expr));
      return makeDynamicCastExpression(
          static_cast<const clang::CXXDynamicCastExpr*>(expr),
          shouldDelay, receiver, guard);
    case clang::Stmt::CharacterLiteralClass:
      { assert(llvm::dyn_cast<clang::CharacterLiteral>(expr));
        const clang::CharacterLiteral* litteralExpr
            = static_cast<const clang::CharacterLiteral*>(expr);
        ikind type = ICHAR;
        if (litteralExpr->getKind() != clang::CharacterLiteral::Ascii) {
          if (litteralExpr->getKind() == clang::CharacterLiteral::Wide)
            type = IWCHAR;
          else {
            std::cerr << "Unsupported character type:";
#if CLANG_VERSION_MAJOR >= 11
            expr->dump(llvm::errs(), *_context);
#else
            expr->dump(llvm::errs(), _context->getSourceManager());
#endif
            std::cerr << "\nAborting\n";
            exit(2);
          };
        };
        return
          guard.setAssignResult(
            exp_node_Constant(
              compilation_constant_IntCst(
                type, ICLITERAL, (int64_t) litteralExpr->getValue())),
            expr);
      };
    case clang::Stmt::CompoundLiteralExprClass:
      assert(llvm::dyn_cast<clang::CompoundLiteralExpr>(expr));
      return makeCompoundLiteralExpression(
          static_cast<const clang::CompoundLiteralExpr*>(expr),
          shouldDelay, receiver, hasImplicitThisStar, guard);
    case clang::Stmt::DeclRefExprClass:
      assert(llvm::dyn_cast<clang::DeclRefExpr>(expr));
      return makeDeclRefExpression(static_cast<const clang::DeclRefExpr*>
          (expr), shouldDelay, receiver, guard);
    case clang::Stmt::FloatingLiteralClass:
      { assert(llvm::dyn_cast<clang::FloatingLiteral>(expr));
        const clang::FloatingLiteral* floatingLitteral
            = static_cast<const clang::FloatingLiteral*>(expr);
        fkind k =
          _clangUtils->makeFloatConstantType(expr->getType().getTypePtr());
        location loc = _clangUtils->makeLocation(expr->getSourceRange());
        llvm::SmallVector<char, 10> result;
        floatingLitteral->getValue().toString(result, 16, 3);
        std::string strResult(result.data(), result.size());
        if (strResult.find_first_of(".EelLfF") == std::string::npos)
          strResult += ".0";
        return guard.setAssignResult(
          makeFloatConstant(loc, k, strResult.data()), expr);
      };
    case clang::Stmt::IntegerLiteralClass:
      { assert(llvm::dyn_cast<clang::IntegerLiteral>(expr));
        ikind kind =
          _clangUtils->makeIntConstantType(expr->getType().getTypePtr());
        const clang::IntegerLiteral* i
            = static_cast<const clang::IntegerLiteral*>(expr);
        return
          guard.setAssignResult(
            exp_node_Constant(
              compilation_constant_IntCst(
                kind, ICLITERAL,
                (int64_t) i->getValue().getLimitedValue(UINT64_MAX))),
            expr);
      };
    case clang::Stmt::MaterializeTemporaryExprClass:
      assert(llvm::dyn_cast<clang::MaterializeTemporaryExpr>(expr));
      return makeMaterializeTemporaryExpression(
          static_cast<const clang::MaterializeTemporaryExpr*>(expr),
          shouldDelay, receiver, guard);
    case clang::Stmt::CXXBindTemporaryExprClass:
      assert(llvm::dyn_cast<clang::CXXBindTemporaryExpr>(expr));
      return makeBindTemporaryExpression(
          static_cast<const clang::CXXBindTemporaryExpr*>(expr),
          shouldDelay, receiver, hasImplicitThisStar, guard);
    case clang::Stmt::MemberExprClass:
      { assert(llvm::dyn_cast<clang::MemberExpr>(expr));
        const clang::MemberExpr* fieldAccessExpr
            = static_cast<const clang::MemberExpr*>(expr);
        bool isReferenceField = _clangUtils->lvalHasRefType(expr);
        clang::ValueDecl* memberDecl = fieldAccessExpr->getMemberDecl();
        clang::Decl::Kind kind = memberDecl->getKind();
        if (kind >= clang::Decl::firstVar && kind <= clang::Decl::lastVar) {
          assert(llvm::dyn_cast<clang::VarDecl>(memberDecl));
          clang::VarDecl* fieldDecl = static_cast<clang::VarDecl*>(memberDecl);
          if (fieldDecl->isStaticDataMember()) {
            exp_node evar =
              exp_node_Variable(
                variable_Global(_clangUtils->makeQualifiedName(*fieldDecl)));
            if (isReferenceField) {
              expression var_expr =
                expression_cons(makeLocation(expr->getSourceRange()), evar);
              evar =
                exp_node_Unary_operator(uokind_UOCastDeref(), var_expr);
            }
            return guard.setAssignResult(evar,expr);
          }
        };
        const clang::CXXRecordDecl* base = fieldAccessExpr->getBase()
            ->getType().getTypePtr()->getPointeeCXXRecordDecl();
        if (!base)
          base = fieldAccessExpr->getBase()->getType().getTypePtr()
              ->getCanonicalTypeInternal().getTypePtr()->getAsCXXRecordDecl();
        if (base) {
          if (hasInstanceContext()) {
            _tableForWaitingDeclarations.ensureGeneration(
              base, unvisitedDecls());
          }
          else if (shouldDelay && !*shouldDelay)
            *shouldDelay = !_tableForWaitingDeclarations.hasVisited(base);
        };
        expression subnode =
          makeLocExpression(fieldAccessExpr->getBase(), shouldDelay,receiver);
        // isArrow distinguishes between x->f and x.f
        // we translate the former as (*x).f
        if (fieldAccessExpr->isArrow()) {
          location base_loc =
            makeLocation(fieldAccessExpr->getBase()->getSourceRange());
          subnode =
            expression_cons(base_loc, exp_node_Dereference(subnode));
        }
        const char* field_name =
          _clangUtils->get_field_name(fieldAccessExpr->getMemberDecl());
        exp_node field_acc = exp_node_FieldAccess(subnode,field_name);
        if (isReferenceField) {
          location loc = makeLocation(expr->getSourceRange());
          expression efield_acc = expression_cons(loc, field_acc);
          field_acc = exp_node_Unary_operator(uokind_UOCastDeref(),efield_acc);
        }
        return guard.setAssignResult(field_acc, expr);
      };
    case clang::Stmt::ParenExprClass:
      { assert(llvm::dyn_cast<clang::ParenExpr>(expr));
        const clang::ParenExpr* subExpr
            = static_cast<const clang::ParenExpr*>(expr);
        return guard.setAssignResult(makeExpression(subExpr->getSubExpr(),
            shouldDelay,receiver), expr);
      };
    case clang::Stmt::PredefinedExprClass:
      { // Only used for the __func__ identifier and its siblings
        // __FUNCTION__ and __PRETTY_FUNCTION__
        // we don't make a distinction between them.
        variable v = variable_Local(qualified_name_cons(NULL,"__func__"));
        return guard.setAssignResult( exp_node_Variable(v), expr);
      }
    case clang::Stmt::UnaryOperatorClass:
      assert(llvm::dyn_cast<clang::UnaryOperator>(expr));
      return makeUnaryOperator(static_cast<const clang::UnaryOperator*>(expr),
          shouldDelay, receiver, guard);
    case clang::Stmt::StringLiteralClass:
      { assert(llvm::dyn_cast<clang::StringLiteral>(expr));
        const clang::StringLiteral* string
          = static_cast<const clang::StringLiteral*>(expr);
        if (string->getCharByteWidth() == 1)
          return guard.setAssignResult(exp_node_String(strdup(string
                ->getString().str().c_str())), expr);
        else {
          std::cerr << "Warning: unsupported constant wide string"
            << std::endl;
          char* result = (char*) malloc(string->getByteLength()
              + string->getCharByteWidth());
          memcpy(result, string->getBytes().data(), string->getByteLength());
          memset(result + string->getByteLength(),0,string->getCharByteWidth());
          return guard.setAssignResult(exp_node_String(result), expr);
        };
      };
    case clang::Stmt::TypeTraitExprClass:
      { assert(llvm::dyn_cast<clang::TypeTraitExpr>(expr));
        const clang::TypeTraitExpr* booleanTraits
          = static_cast<const clang::TypeTraitExpr*>(expr);
        compilation_constant cst =
          compilation_constant_IntCst(IBOOL, ICSTATICCONST,
            booleanTraits->getValue());
        return guard.setAssignResult(exp_node_Constant(cst), expr);
      }
    case clang::Stmt::SubstNonTypeTemplateParmExprClass: {
      auto targ = static_cast<const clang::SubstNonTypeTemplateParmExpr*>(expr);
      exp_node e = makeExpression(targ->getReplacement(), shouldDelay);
      return guard.setAssignResult(e,expr);
    }
    case clang::Stmt::VAArgExprClass:
      { assert (llvm::dyn_cast<clang::VAArgExpr>(expr));
        const clang::VAArgExpr* va_arg
          = static_cast<const clang::VAArgExpr*>(expr);
        expression subexpr = makeLocExpression(va_arg->getSubExpr(),
            shouldDelay);
        clang::QualType va_arg_type = va_arg->getWrittenTypeInfo()->getType();
        qual_type exp_type = makeDefaultType(va_arg->getExprLoc(), va_arg_type);
        return guard.setAssignResult( exp_node_VAArg(subexpr, exp_type), expr);
      }
    case clang::Stmt::ImplicitValueInitExprClass:
      assert(llvm::dyn_cast<clang::ImplicitValueInitExpr>(expr));
      return makeImplicitValueInitExpression(
          static_cast<const clang::ImplicitValueInitExpr*>(expr),
          shouldDelay, receiver, guard);
    case clang::Stmt::UnaryExprOrTypeTraitExprClass:
      assert(llvm::dyn_cast<clang::UnaryExprOrTypeTraitExpr>(expr));
      return makeUnaryExprOrTypeTraitExpression(
          static_cast<const clang::UnaryExprOrTypeTraitExpr*>(expr),
          shouldDelay, receiver, guard);
    case clang::Stmt::AtomicExprClass:
      assert(llvm::dyn_cast<clang::AtomicExpr>(expr));
      { const clang::AtomicExpr* thisExpr
          = static_cast<const clang::AtomicExpr*>(expr);
        clang::IdentifierInfo* info = NULL;
        switch (thisExpr->getOp()) {
          case clang::AtomicExpr::AO__atomic_load:
            info = &_context->Idents.get("__atomic_load");
            break;
          case clang::AtomicExpr::AO__atomic_load_n:
            info = &_context->Idents.get("__atomic_load_n");
            break;
          case clang::AtomicExpr::AO__atomic_store:
            info = &_context->Idents.get("__atomic_store");
            break;
          case clang::AtomicExpr::AO__atomic_store_n:
            info = &_context->Idents.get("__atomic_store_n");
            break;
          case clang::AtomicExpr::AO__atomic_exchange:
            info = &_context->Idents.get("__atomic_exchange");
            break;
          case clang::AtomicExpr::AO__atomic_exchange_n:
            info = &_context->Idents.get("__atomic_exchange_n");
            break;
          case clang::AtomicExpr::AO__atomic_compare_exchange:
            info = &_context->Idents.get("__atomic_compare_exchange");
            break;
          case clang::AtomicExpr::AO__atomic_compare_exchange_n:
            info = &_context->Idents.get("__atomic_compare_exchange_n");
            break;
          case clang::AtomicExpr::AO__atomic_fetch_add:
            info = &_context->Idents.get("__atomic_fetch_add");
            break;
          case clang::AtomicExpr::AO__atomic_fetch_sub:
            info = &_context->Idents.get("__atomic_fetch_sub");
            break;
          case clang::AtomicExpr::AO__atomic_fetch_and:
            info = &_context->Idents.get("__atomic_fetch_and");
            break;
          case clang::AtomicExpr::AO__atomic_fetch_or:
            info = &_context->Idents.get("__atomic_fetch_or");
            break;
          case clang::AtomicExpr::AO__atomic_fetch_xor:
            info = &_context->Idents.get("__atomic_fetch_xor");
            break;
          case clang::AtomicExpr::AO__atomic_fetch_nand:
            info = &_context->Idents.get("__atomic_fetch_nand");
            break;
          case clang::AtomicExpr::AO__atomic_add_fetch:
            info = &_context->Idents.get("__atomic_add_fetch");
            break;
          case clang::AtomicExpr::AO__atomic_sub_fetch:
            info = &_context->Idents.get("__atomic_sub_fetch");
            break;
          case clang::AtomicExpr::AO__atomic_and_fetch:
            info = &_context->Idents.get("__atomic_and_fetch");
            break;
          case clang::AtomicExpr::AO__atomic_or_fetch:
            info = &_context->Idents.get("__atomic_or_fetch");
            break;
          case clang::AtomicExpr::AO__atomic_xor_fetch:
            info = &_context->Idents.get("__atomic_xor_fetch");
            break;
          case clang::AtomicExpr::AO__atomic_nand_fetch:
            info = &_context->Idents.get("__atomic_nand_fetch");
            break;
          default:
            std::cerr << "Unsupported atomic builtin:";
#if CLANG_VERSION_MAJOR >= 11
            expr->dump(llvm::errs(), *_context);
#else
            expr->dump(llvm::errs(), _context->getSourceManager());
#endif
            std::cerr << "\nAborting\n";
            exit(2);
        };
        clang::LookupResult R(*_sema, info, expr->getSourceRange().getBegin(),
               clang::Sema::LookupOrdinaryName);
        const clang::DeclContext* context = _context->getTranslationUnitDecl();
        if (_sema->LookupQualifiedName(R, const_cast<clang::DeclContext*>
            (context))) {
          if (R.getResultKind() == clang::LookupResult::Found) {
            assert(llvm::dyn_cast<clang::FunctionDecl>(
              R.getFoundDecl()));
            ensureBuiltinDeclaration(
              (clang::Builtin::ID) ((thisExpr->getOp()
                  - clang::AtomicExpr::AO__atomic_load)
                  + clang::Builtin::BI__atomic_load),
              static_cast<const clang::FunctionDecl*>(R.getFoundDecl()),
              true /* doesForceVariadic */);
          };
        };
      };
      return makeAtomicExprExpression(static_cast<const clang::AtomicExpr*>(
          expr), shouldDelay, receiver, guard);
    case clang::Stmt::ExprWithCleanupsClass:
      { assert (llvm::dyn_cast<clang::ExprWithCleanups>(expr));
        const clang::ExprWithCleanups* sexpr
          = static_cast<const clang::ExprWithCleanups*>(expr);
        _cleanups.push_back(sexpr);
        exp_node subnode = makeExpression(sexpr->getSubExpr(),
            shouldDelay, receiver);
        return guard.setAssignResult(subnode, expr);
      }
    case clang::Stmt::CXXScalarValueInitExprClass:
      { assert (llvm::dyn_cast<clang::CXXScalarValueInitExpr>(expr));
        const clang::CXXScalarValueInitExpr* sexpr
          = static_cast<const clang::CXXScalarValueInitExpr*>(expr);
        clang::QualType type = sexpr->getTypeSourceInfo()->getType();
        if (_clangUtils->isArithmeticType(type.getTypePtr())) {
          typ pltype = _clangUtils->makeArithmeticType(type.getTypePtr());
          if (pltype->tag_typ == INT) {
            ikind kind = pltype->cons_typ.Int.kind;
            free_typ(pltype);
            return
              guard.setAssignResult(exp_node_Constant(
                  compilation_constant_IntCst(
                    kind, ICLITERAL,
                    (int64_t) 0)),
                expr);
          }
          else if (pltype->tag_typ == FLOAT) {
            fkind kind = pltype->cons_typ.Float.kind;
            location loc = _clangUtils->makeLocation(expr->getSourceRange());
            expression zero = makeFloatZero(loc,kind);
            free_location(loc);
            free_typ(pltype);
            return guard.setAssignResult(zero,expr);
          }
          else
            { assert(false); }
        }
        else if (_clangUtils->isPointerType(type.getTypePtr())) {
          return guard.setAssignResult(
            makeNullPointer(
              _clangUtils->makeLocation(expr->getSourceRange()),
              _clangUtils->makeType(expr->getExprLoc(), type)),
            expr);
        }
        assert(false);
      };
    case clang::Stmt::CXXDefaultInitExprClass:
      { assert (llvm::dyn_cast<clang::CXXDefaultInitExpr>(expr));
        const clang::CXXDefaultInitExpr* sexpr
        = static_cast<const clang::CXXDefaultInitExpr*>(expr);
        if(sexpr->getExpr()->getStmtClass() == clang::Stmt::InitListExprClass) {
            _implicitThisStar = guard.releaseExpr();
            return  makeExpression(
                      sexpr->getExpr(),
                      shouldDelay,
                      receiver);
        }
        else {
          return  guard.setAssignResult(
                    makeExpression(
                      sexpr->getExpr(),
                      shouldDelay,
                      receiver),
                    expr);
        }
      };
    case clang::Stmt::InitListExprClass:
      { assert (llvm::dyn_cast<clang::InitListExpr>(expr));
        const clang::InitListExpr* sexpr
            = static_cast<const clang::InitListExpr*>(expr);
        assert(sexpr->getNumInits());
        switch(_memberType) {
          case clang::Type::ConstantArray:
            { expression field = guard.releaseExpr();
              location loc = makeLocation(expr->getSourceRange());
              exp_node all_init = NULL;
              for(unsigned i=0; i<sexpr->getNumInits(); ++i) {
                expression index = makeIntLiteral(loc,IULONG,i);
                if(!i) {
                  all_init =
                    exp_node_Assign(
                      expression_cons(
                        copy_loc(loc),
                        exp_node_ArrayAccess(
                          field,
                          index)),
                      expression_cons(
                        copy_loc(loc),
                        makeExpression(
                          sexpr->getInit(0),
                          shouldDelay,
                          receiver)));
                }
                else {
                  all_init =
                    exp_node_Binary_operator(
                      BOCOMMA,
                      AKRVALUE,
                      expression_cons(
                        copy_loc(loc),
                        all_init),
                      expression_cons(
                        copy_loc(loc),
                        exp_node_Assign(
                          expression_cons(
                            copy_loc(loc),
                            exp_node_ArrayAccess(
                              field,
                              index)),
                          expression_cons(
                            copy_loc(loc),
                            makeExpression(
                              sexpr->getInit(i),
                              shouldDelay,
                              receiver)))));
                }
              }
              free_location(loc);
              return all_init;
            }
          case clang::Type::Record:
            std::cerr <<
            "Unsupported type (record) for default init with braces"
            << std::endl;
            return NULL;
          default:
            return  guard.setAssignResult(
                      makeExpression(
                        sexpr->getInit(0),
                        shouldDelay,
                        receiver),
                      expr);
        }
      };
    case clang::Stmt::StmtExprClass:
      { assert (llvm::dyn_cast<clang::StmtExpr>(expr));
        const clang::StmtExpr* sexpr
            = static_cast<const clang::StmtExpr*>(expr);
        return exp_node_GnuBody(
                 cons_container(
                   makeStmt(
                     sexpr->getSubStmt(),
                     NULL,
                     _context->getTranslationUnitDecl(),
                     shouldDelay),
                     NULL));
      }
    case clang::Stmt::ShuffleVectorExprClass:
      { assert (llvm::dyn_cast<clang::ShuffleVectorExpr>(expr));
        const clang::ShuffleVectorExpr* sexpr
            = static_cast<const clang::ShuffleVectorExpr*>(expr);
        // [TODO] the semantics is not the correct one !
        return  guard.setAssignResult(
          makeExpression(sexpr->getExpr(0), shouldDelay, receiver), expr);
      }
    case clang::Stmt::ConvertVectorExprClass:
      { assert (llvm::dyn_cast<clang::ConvertVectorExpr>(expr));
        const clang::ConvertVectorExpr* sexpr
            = static_cast<const clang::ConvertVectorExpr*>(expr);
        // [TODO] the semantics is not the correct one !
        clang::QualType destinationType = sexpr->getTypeSourceInfo()
          ->getType();
        qual_type resultType =
          makeDefaultType(sexpr->getExprLoc(), destinationType);
        return guard.setAssignResult(
          exp_node_PointerCast(resultType,
            reference_or_pointer_kind_RPKPointer(),
            expression_cons(makeLocation(expr->getSourceRange()),
              makeExpression(sexpr->getSrcExpr(), shouldDelay, receiver))),
          expr);
      }
    case clang::Stmt::CXXStdInitializerListExprClass:
      {
        const clang::CXXStdInitializerListExpr* il =
          static_cast<const clang::CXXStdInitializerListExpr*>(expr);
        return guard.setAssignResult(make_initializer_list(il), expr);
      }
    case clang::Stmt::LambdaExprClass: {
      auto lam = static_cast<const clang::LambdaExpr*>(expr);
      return guard.setAssignResult(make_lambda_expr(lam), expr);
    }
    case clang::Stmt::AddrLabelExprClass:
    case clang::Stmt::DesignatedInitExprClass:
    case clang::Stmt::FunctionParmPackExprClass:
    case clang::Stmt::OpaqueValueExprClass:
    case clang::Stmt::ParenListExprClass:
    default: {}
  }
  std::cerr << "Unsupported expression:";
#if CLANG_VERSION_MAJOR >= 11
  expr->dump(llvm::errs(), *_context);
#else
  expr->dump(llvm::errs(), _context->getSourceManager());
#endif
  std::cerr << "\nAborting\n";
  exit(2);
}

compilation_constant FramacVisitor::makeConstantExpression(
  const clang::Expr* expr) const {
  clang::APValue result;
  if (expr->isCXX11ConstantExpr(*_context,&result)) {
    switch(result.getKind()) {
      // if the expression is a C++11 constant expression, the result
      // ought to be initialized by isCXX11ConstantExpr
#if CLANG_VERSION_MAJOR < 9
      case clang::APValue::Uninitialized: assert(false);
#else
      case clang::APValue::None:
      case clang::APValue::Indeterminate: assert(false);
#endif
      case clang::APValue::Int: {
        const llvm::APSInt& v = result.getInt();
        ikind kind =
          _clangUtils->makeIntConstantType(expr->getType().getTypePtr());
        return
          compilation_constant_IntCst(
            kind, ICLITERAL, v.getLimitedValue(UINT64_MAX));
      }
      case clang::APValue::Float: {
        const llvm::APFloat& v = result.getFloat();
        llvm::SmallVector<char,10> repr;
        v.toString(repr);
        fkind kind =
          _clangUtils->makeFloatConstantType(expr->getType().getTypePtr());
        return compilation_constant_FloatCst(kind, repr.data());
      }
      case clang::APValue::ComplexInt:
      case clang::APValue::ComplexFloat:
      case clang::APValue::LValue:
      case clang::APValue::Vector:
      case clang::APValue::Array:
      case clang::APValue::Struct:
      case clang::APValue::Union:
      case clang::APValue::MemberPointer:
      case clang::APValue::AddrLabelDiff:
#if CLANG_VERSION_MAJOR >= 9
      case clang::APValue::FixedPoint:
#endif
        {
          std::cerr << "unsupported constant expression: ";
          expr->dump();
          expr->dump();
          std::cerr << "\nAborting\n";
          exit(2);
        }
      default:
        break;
    }
  };
  std::cerr << "constant expression cannot be evaluated at compile-time";
  expr->dump();
  std::cerr << "\nAborting\n";
  exit(2);
}

cond_statement FramacVisitor::makeCondition(
  const clang::VarDecl* var_decl, expression e, bool* shouldDelay) {
  if (var_decl) {
    qual_type typ =
      makeDefaultType(
        var_decl->getLocation(), var_decl->getType());
    const char* name = copy_string(var_decl->getNameAsString());
    makeImplicitThis(var_decl);
    init_expr init =
      makeInitExpr(var_decl->getType(),var_decl->getInit(), shouldDelay);
    return cond_statement_CondVarDecl(name, typ, init);
  }
  else {
    return cond_statement_CondExpression(e);
  }
}

void FramacVisitor::makeImplicitThis(const clang::VarDecl* vdec) const {
  if (isRecordOrRecordRef(vdec->getType().getTypePtr()) ||
    _clangUtils->isConstantArrayType(vdec->getType().getTypePtr()))
  { location loc = makeLocation(vdec->getSourceRange());
    variable v = variable_Local(_clangUtils->makeQualifiedName(*vdec));
    expression var = expression_cons(loc,exp_node_Variable(v));
    _implicitThisStar = var;
  };
}

void FramacVisitor::readStatementCommentUntil(
    clang::SourceLocation sourceLocation, location& commentLocation,
    list& /*<statement>*/stmts, ForwardReferenceList& forwardStmts,
    const clang::Stmt* nextStmt, ForwardReferenceList* container,
    const clang::DeclContext* context) {
  // implicit precondition: commentLocation != NULL => stmts != NULL
  // the reverse is not true any more thanks to cleanups
  int previousTemplateComment = _templateCommentIndex,
      previousComment = _commentIndex;
  advanceCommentUntil(sourceLocation);

  while (previousTemplateComment < _templateCommentIndex) {
    ++previousTemplateComment;
    switch (_annotationCommentList[previousTemplateComment]->getKind()) {
      case AnnotationComment::KGlobal:
        parseGlobalComment(*_annotationCommentList[previousTemplateComment],
            context);
        break;
      case AnnotationComment::KGhost:
        parseGhostStatement(
          *_annotationCommentList[previousTemplateComment],
          context,
          container ? container : &forwardStmts);
        if (!container && stmts) {
          statement s = (statement) stmts->element.container;
          assert(s->tag_statement == GHOST_BLOCK);
          commentLocation = s->cons_statement.Ghost_block.loc;
        }
        break;

      case AnnotationComment::KLabel: // assert
        parseCodeAnnotation(*_annotationCommentList[previousTemplateComment],
            context, container ? container : &forwardStmts);
        if (!container && stmts) {
          assert(((statement) stmts->element.container)->tag_statement
              == CODE_ANNOT);
          commentLocation = ((statement) stmts->element.container)
            ->cons_statement.Code_annot.loc;
        };
        break;
      case AnnotationComment::KNextLoop:
        if (!nextStmt)
          parseDefaultComment(*_annotationCommentList[previousTemplateComment]);
        else {
          parseLoopAnnotation(*_annotationCommentList[previousTemplateComment],
              nextStmt, context, container ? container : &forwardStmts);
          if (!container && stmts) {
            assert(((statement) stmts->element.container)->tag_statement
                == CODE_ANNOT);
            commentLocation = ((statement) stmts->element.container)
              ->cons_statement.Code_annot.loc;
          };
        };
        break;
      case AnnotationComment::KNext:
      case AnnotationComment::KNextStatement:
        if (!nextStmt)
          parseDefaultComment(*_annotationCommentList[previousTemplateComment]);
        else {
          parseStatementAnnotation(
              *_annotationCommentList[previousTemplateComment],
              nextStmt, context, container ? container : &forwardStmts);
          if (!container && stmts) {
            assert(((statement) stmts->element.container)->tag_statement
                == CODE_ANNOT);
            commentLocation = ((statement) stmts->element.container)
              ->cons_statement.Code_annot.loc;
          };
        };
        break;
      case AnnotationComment::KOuterLoop:
        { std::cerr << "unimplemented next attachment" << std::endl;
          exit(2);
          assert(false);
          // Acsl::FunctionContract functionContract(Decl);
          // Acsl::Parser parser(Decl->getDeclContext(), _context, _sema,
          //    _parents.getScope(), functionContract);
          // parser.parse(*_annotationCommentList[previousTemplateComment]
          //    .getContent());
        };
        break;
      default:
        parseDefaultComment(*_annotationCommentList[previousTemplateComment]);
        break;
    };
  };

  while (previousComment < _commentIndex) {
    ++previousComment;
    switch (_annotationCommentList[previousComment]->getKind()) {
      case AnnotationComment::KGlobal:
        parseGlobalComment(*_annotationCommentList[previousComment], context);
        break;
      case AnnotationComment::KGhost:
        parseGhostStatement(
          *_annotationCommentList[previousComment],
          context,
          container ? container : &forwardStmts);
        if (!container && stmts) {
          statement s = (statement) stmts->element.container;
          assert (s->tag_statement == GHOST_BLOCK);
          commentLocation = s->cons_statement.Ghost_block.loc;
        }
        break;
      case AnnotationComment::KLabel:
        parseCodeAnnotation(*_annotationCommentList[previousComment], context,
            container ? container : &forwardStmts);
        break;
      case AnnotationComment::KNextLoop:
        if (!nextStmt)
          parseDefaultComment(*_annotationCommentList[previousComment]);
        else {
          parseLoopAnnotation(*_annotationCommentList[previousComment],
              nextStmt, context, container ? container : &forwardStmts);
          if (!container && stmts) {
            assert(((statement) stmts->element.container)->tag_statement
                == CODE_ANNOT);
            commentLocation = ((statement) stmts->element.container)
              ->cons_statement.Code_annot.loc;
          };
        };
        break;
      case AnnotationComment::KNext:
      case AnnotationComment::KNextStatement:
        if (!nextStmt)
          parseDefaultComment(*_annotationCommentList[previousComment]);
        else {
          parseStatementAnnotation(
              *_annotationCommentList[previousComment],
              nextStmt, context, container ? container : &forwardStmts);
          if (!container && stmts) {
            assert(((statement) stmts->element.container)->tag_statement
                == CODE_ANNOT);
            commentLocation = ((statement) stmts->element.container)
              ->cons_statement.Code_annot.loc;
          };
        };
        break;
      case AnnotationComment::KOuterLoop:
      default:
        parseDefaultComment(*_annotationCommentList[previousComment]);
        break;
    };
  };
}

statement FramacVisitor::makeExprWithCleanupsStmt(
    const clang::ExprWithCleanups* cleanups, location l,
    list& /*<statement>*/stmts, ForwardReferenceList& forwardStmts,
    const clang::DeclContext* context, bool* shouldDelay) {
  unsigned numDecls = cleanups->getNumObjects();
  const clang::Expr* mainExpr = cleanups->getSubExpr();
  _parents.pushBlock();
  // /* statement */ list* cursor = forwardStmts.getBack()
  //   ? &forwardStmts.getBack()->next : &forwardStmts.getFront();
  statement body = makeStmt(mainExpr,&forwardStmts, context, shouldDelay);
  forwardStmts.insertContainer(body);
  forwardStmts.advanceToEnd();
  for (unsigned declIndex = 0; declIndex < numDecls; ++declIndex) {
#if CLANG_VERSION_MAJOR >= 11
    clang::BlockDecl* decl = cleanups->getObject(declIndex).get<clang::BlockDecl*>();
#else
    clang::BlockDecl* decl = cleanups->getObject(declIndex);
#endif
    statement body = makeStmt(decl->getBody(), &forwardStmts, context,
        shouldDelay);
    forwardStmts.insertContainer(body);
  };
  _parents.popBlock();
  return statement_Block(l, stmts);
}

void FramacVisitor::makeCleanupsStmts(
    ForwardReferenceList& forwardStmts, /* stmt */ list* cursor,
    expression expr, const clang::DeclContext* context, bool* shouldDelay) {
  bool isLast = !forwardStmts.getBack()
    || cursor == &forwardStmts.getBack()->next;
  if (isLast)
    forwardStmts.advanceToEnd();
  std::vector<const clang::ExprWithCleanups*>::const_iterator
      iterEnd = _cleanups.end(), iter = _cleanups.begin();
  for (; iter != iterEnd; ++iter) {
    const clang::ExprWithCleanups& cleanup = **iter;
    unsigned numDecls = cleanup.getNumObjects();
    for (unsigned declIndex = 0; declIndex < numDecls; ++declIndex) {
#if CLANG_VERSION_MAJOR >= 11
      clang::BlockDecl* decl = cleanup.getObject(declIndex).get<clang::BlockDecl*>();
#else
      clang::BlockDecl* decl = cleanup.getObject(declIndex);
#endif
      statement body = makeStmt(decl->getBody(), &forwardStmts, context,
          shouldDelay);
      forwardStmts.insertContainer(body);
    };
  };
  _cleanups.clear();
}

void FramacVisitor::makeCleanupsStmts(
    ForwardReferenceList& forwardStmts, /* stmt */ list* cursor,
    init_expr iexpr, const clang::DeclContext* context, bool* shouldDelay) {
  bool isLast = !forwardStmts.getBack()
    || cursor == &forwardStmts.getBack()->next;
  if (isLast)
    forwardStmts.advanceToEnd();
  std::vector<const clang::ExprWithCleanups*>::const_iterator
      iterEnd = _cleanups.end(), iter = _cleanups.begin();
  for (; iter != iterEnd; ++iter) {
    const clang::ExprWithCleanups& cleanup = **iter;
    unsigned numDecls = cleanup.getNumObjects();
    for (unsigned declIndex = 0; declIndex < numDecls; ++declIndex) {
#if CLANG_VERSION_MAJOR >= 11
      clang::BlockDecl* decl = cleanup.getObject(declIndex).get<clang::BlockDecl*>();
#else
      clang::BlockDecl* decl = cleanup.getObject(declIndex);
#endif
      statement body = makeStmt(decl->getBody(), &forwardStmts, context,
          shouldDelay);
      forwardStmts.insertContainer(body);
    };
  };
  _cleanups.clear();
}

void FramacVisitor::makeCleanupsStmts(
    ForwardReferenceList& forwardStmts, /* stmt */ list* cursor,
    /* expression */ list exprs, const clang::DeclContext* context,
    bool* shouldDelay) {
  // list exprCursor = exprs;
  bool isLast = !forwardStmts.getBack()
    || cursor == &forwardStmts.getBack()->next;
  if (isLast)
    forwardStmts.advanceToEnd();
  std::vector<const clang::ExprWithCleanups*>::const_iterator
      iterEnd = _cleanups.end(), iter = _cleanups.begin();
  for (; iter != iterEnd; ++iter) {
    const clang::ExprWithCleanups& cleanup = **iter;
    unsigned numDecls = cleanup.getNumObjects();
    for (unsigned declIndex = 0; declIndex < numDecls; ++declIndex) {
#if CLANG_VERSION_MAJOR >= 11
      clang::BlockDecl* decl = cleanup.getObject(declIndex).get<clang::BlockDecl*>();
#else
      clang::BlockDecl* decl = cleanup.getObject(declIndex);
#endif
      statement body = makeStmt(decl->getBody(), &forwardStmts, context,
          shouldDelay);
      forwardStmts.insertContainer(body);
    };
  };
  _cleanups.clear();
}

statement FramacVisitor::makeCompoundStmt(
  const clang::CompoundStmt* block,
  location l, location commentLocation, list& /*<statement>*/stmts,
  ForwardReferenceList* container, ForwardReferenceList& forwardStmts,
  const clang::DeclContext* context, bool* shouldDelay)
{ _parents.pushBlock();
  addLabelsInSema(block);
  clang::CompoundStmt::const_body_iterator it = block->body_begin();
  clang::CompoundStmt::const_body_iterator last = block -> body_end();
  while(it < last) {
    statement stmt = makeStmt(*it, &forwardStmts, context, shouldDelay);
    forwardStmts.insertContainer(stmt);
    it++;
  }
  _parents.popBlock();
  readStatementCommentUntil(block->getSourceRange().getEnd(),
    commentLocation, stmts, forwardStmts, NULL, container, context);
  return statement_Block(l, stmts);
}

statement FramacVisitor::makeReturnStmt(
  const clang::ReturnStmt* returnStmt,
  location l, location commentLocation, list& /*<statement>*/stmts,
  ForwardReferenceList& forwardStmts, const clang::DeclContext* context,
  bool* shouldDelay) {
  // implicit precondition: commentLocation != NULL => stmts != NULL
  // the reverse is not true any more thanks to cleanups
  const clang::Expr* re = returnStmt->getRetValue();
  expression result = re ? makeLocExpression(re, shouldDelay) : NULL;
  option e = re ? opt_some_container(result) : opt_none();
  if (stmts || !_cleanups.empty()) {
    /* statement */ list* cursor = forwardStmts.getBack()
      ? &forwardStmts.getBack()->next : &forwardStmts.getFront();
    forwardStmts.insertContainer(statement_Return(l,e));
    if (!_cleanups.empty()) {
      assert(result);
      makeCleanupsStmts(forwardStmts, cursor, result, context, shouldDelay);
    };
    if (commentLocation) {
      commentLocation = copy_loc(commentLocation);
      extend_location_with(commentLocation, l);
    }
    else
      commentLocation = copy_loc(l);
  };
  return !stmts ? statement_Return(l,e)
                : statement_Block(commentLocation, stmts);
}

statement FramacVisitor::makeDeclStmt(
  const clang::DeclStmt* declStmt, location l, location commentLocation,
  list& /*<statement>*/stmts, ForwardReferenceList* container,
  ForwardReferenceList& forwardStmts,
  const clang::DeclContext* context, bool* shouldDelay) {
  // implicit precondition: commentLocation != NULL => stmts != NULL
  // the reverse is not true any more thanks to cleanups
  if (declStmt->isSingleDecl()) {
    clang::Decl* singleDecl=const_cast<clang::Decl*>(declStmt->getSingleDecl());
    _parents.addDecl(singleDecl);
    clang::Decl::Kind kindDecl = singleDecl->getKind();
    if (kindDecl >= clang::Decl::firstVar && kindDecl <= clang::Decl::lastVar) {
      assert(llvm::dyn_cast<clang::VarDecl>(singleDecl));
      const clang::VarDecl* varDecl
          = static_cast<const clang::VarDecl*>(singleDecl);
      qual_type type =
        makeDefaultType(varDecl->getLocation(), varDecl->getType());
      if (varDecl->isStaticLocal()) {
        type->qualifier = cons_plain(STATIC,type->qualifier);
      }
      const char* name = strdup(varDecl->getName().str().c_str());
      if (stmts) {
        commentLocation = commentLocation
          ? copy_loc(commentLocation) : copy_loc(l);
        extend_location_with(commentLocation, l);
      };
      if (varDecl->hasInit()) {
        makeImplicitThis(varDecl);
        const clang::ConstantArrayType* constantArrayType
            = _clangUtils->isConstantArrayType(varDecl->getType().getTypePtr());
        if (!constantArrayType) {
          option /*init_expr*/ init =
            opt_some_container(
              makeInitExpr(
                varDecl->getType(), varDecl->getInit(), shouldDelay));
          bool shouldGenerateBlock = false;
          if (stmts || !_cleanups.empty()) {
            /* statement */ list* containerCursor = NULL;
            if (container) {
              container->append(forwardStmts);
              containerCursor = container->getBack() ?
                &container->getBack()->next : &container->getFront();
              stmts = NULL;
              forwardStmts = ForwardReferenceList(stmts);
              shouldGenerateBlock = true;
            };
            /* statement */ list* cursor = forwardStmts.getBack()
              ? &forwardStmts.getBack()->next : &forwardStmts.getFront();
            (container ? *container : forwardStmts).insertContainer(
                statement_VarDecl(l,name, type, init));
            if (!_cleanups.empty()) {
              makeCleanupsStmts(forwardStmts, cursor,
                (init_expr) init->content.container, context, shouldDelay);
              if (container) {
                assert(containerCursor);
                while (stmts && ((statement) stmts->element.container)
                    ->tag_statement == VARDECL) {
                  statement current = (statement) stmts->element.container;
                  /* statement */ list next = *containerCursor;
                  *containerCursor = cons_container(current, next);
                  /* statement */ list old = stmts;
                  stmts = stmts->next;
                  free(old);
                };
                container->advanceToEnd();
              };
            };
            if ((stmts || shouldGenerateBlock) && !commentLocation)
              commentLocation = copy_loc(l);
          };
          return (!stmts && !shouldGenerateBlock)
              ? statement_VarDecl(l, name, type, init)
              : ((stmts)
                 ? statement_Block(commentLocation, stmts)
                 : statement_Nop(commentLocation)
                 );
        }
        else {
          statement resultDecl = statement_VarDecl(l, name, type, opt_none());
          if (container)
            container->insertContainer(resultDecl);
          else
            forwardStmts.insertContainer(resultDecl);
          expression lvalueThisStar = _implicitThisStar;
          _implicitThisStar = NULL;
          _isImplicitThisBare = false;
          /* statement */ list localStmts = NULL;
          exp_node tmpNode = makeConstantArrayInitExpression(*constantArrayType,
            varDecl->getInit(), lvalueThisStar, shouldDelay, &localStmts);
          free_exp_node(tmpNode);
          if (localStmts) {
            ForwardReferenceList local(localStmts);
            forwardStmts.append(local);
            if (!commentLocation)
              commentLocation = copy_loc(l);
          };
          return statement_Block(commentLocation, stmts);
        };
      };
      if (stmts) {
        forwardStmts.insertContainer(statement_VarDecl(l,name,type,opt_none()));
        free_location(commentLocation);
      };
      return !stmts ? statement_VarDecl(l,name,type,opt_none())
                    : statement_Block(commentLocation, stmts);
    };
  };

  clang::DeclStmt::const_decl_iterator iter_end = declStmt->decl_end();
  // the very first statement can reuse the location l directly. Afterwards,
  // we need to perform copies to avoid sharing.
  bool isAfterFirst = false;
  for (clang::DeclStmt::const_decl_iterator iter = declStmt->decl_begin();
      iter != iter_end; ++iter) {
    if (!isAfterFirst)
      isAfterFirst = true;
    else
      l = copy_loc(l);
    clang::Decl* singleDecl = *iter;
    _parents.addDecl(singleDecl);
    clang::Decl::Kind kindDecl = singleDecl->getKind();
    if (kindDecl >= clang::Decl::firstVar && kindDecl <= clang::Decl::lastVar) {
      assert(llvm::dyn_cast<clang::VarDecl>(singleDecl));
      const clang::VarDecl* varDecl
          = static_cast<const clang::VarDecl*>(singleDecl);
      qual_type type =
        makeDefaultType(varDecl->getLocation(), varDecl->getType());
      const char* name = strdup(varDecl->getName().str().c_str());
      option init = opt_none();
      if (varDecl->hasInit()) {
        makeImplicitThis(varDecl);
        init =
          opt_some_container(
            makeInitExpr(varDecl->getType(), varDecl->getInit(), shouldDelay));
      };
      if (container) {
        /* statement */ list* cursor = container->getBack()
          ? &container->getBack()->next : &container->getFront();
        container->insertContainer(statement_VarDecl(l,name,type,init));
        if (!_cleanups.empty())
          makeCleanupsStmts(*container, cursor,
            (init_expr) init->content.container, context, shouldDelay);
      }
      else {
        /* statement */ list* cursor = forwardStmts.getBack()
          ? &forwardStmts.getBack()->next : &forwardStmts.getFront();
        forwardStmts.insertContainer(statement_VarDecl(l,name,type,init));
        if (!_cleanups.empty())
          makeCleanupsStmts(forwardStmts, cursor,
            (init_expr) init->content.container, context, shouldDelay);
      };
    };
  };
  if (!container)
    return statement_Block(l, stmts);

  if (stmts) {
    if (commentLocation) {
      commentLocation = copy_loc(commentLocation);
      extend_location_with(commentLocation, l);
      free_location(l);
    }
    else
      commentLocation = l;
  };
  return !stmts ? statement_Nop(isAfterFirst ? copy_loc(l) : l)
                : statement_Block(commentLocation, stmts);
}

statement FramacVisitor::makeDoStmt(
  const clang::DoStmt* doStmt, location l,
  location commentLocation, list& /*<statement>*/stmts,
  ForwardReferenceList& forwardStmts, const clang::DeclContext* context,
  bool* shouldDelay) {
  // implicit precondition: commentLocation != NULL => stmts != NULL
  // the reverse is not true any more thanks to cleanups
  exp_node condition = makeExpression(doStmt->getCond(), shouldDelay);
  const char* conditionVarname = NULL;
  /* statement */ list* cursor = NULL;
  if (!_cleanups.empty()) {
    cursor = forwardStmts.getBack()
      ? &forwardStmts.getBack()->next : &forwardStmts.getFront();
    conditionVarname = mk_tmp_name ();
    forwardStmts.insertContainer(statement_VarDecl(copy_loc(l),
        conditionVarname, qual_type_cons(NULL, typ_Int(IBOOL)), opt_none()));
  };
  expression econdition = expression_cons(makeLocation(
      doStmt->getCond()->getSourceRange()), condition);
  statement body = makeStmt(doStmt->getBody(),NULL, context, shouldDelay);
  if (!_cleanups.empty()) {
    if (body->tag_statement != BLOCK)
      body = statement_Block(copy_loc(l), cons_container(body, NULL));
    ForwardReferenceList block(body->cons_statement.Block.instructions);
    block.insertContainer(statement_Expression(copy_loc(econdition->eloc),
      expression_cons(copy_loc(econdition->eloc), exp_node_Assign(
          expression_cons(copy_loc(econdition->eloc), exp_node_Variable(
              variable_Local(qualified_name_cons(NULL,
                strdup(conditionVarname))))),
          econdition))));
    makeCleanupsStmts(block, cursor, econdition, context, shouldDelay);
    econdition = expression_cons(copy_loc(econdition->eloc),
      exp_node_Variable(variable_Local(qualified_name_cons(NULL,
        strdup(conditionVarname)))));
  };
  statement result = statement_DoWhile(l,econdition,body,NULL);
  _delayedLoopAnnotation.attachTo(doStmt, result);
  if (stmts) {
    forwardStmts.insertContainer(result);
    if (commentLocation) {
      commentLocation = copy_loc(commentLocation);
      extend_location_with(commentLocation, l);
    }
    else
      commentLocation = copy_loc(l);
  };
  return !stmts ? result : statement_Block(commentLocation, stmts);
}

statement FramacVisitor::makeForStmt(
  const clang::ForStmt* forStmt, location l, location commentLocation,
  list& /*<statement>*/stmts, ForwardReferenceList& forwardStmts,
  const clang::DeclContext* context, bool* shouldDelay) {
  // implicit precondition: commentLocation != NULL => stmts != NULL
  // the reverse is not true any more thanks to cleanups
  init_statement init = NULL;
  if (!forStmt->getInit())
    init = init_statement_INop();
  else {
    clang::Stmt::StmtClass initClass = forStmt->getInit()->getStmtClass();
    if (initClass == clang::Stmt::DeclStmtClass) {
      assert(llvm::dyn_cast<clang::DeclStmt>(forStmt->getInit()));
      const clang::DeclStmt* declStmt
        = static_cast<const clang::DeclStmt*>(forStmt->getInit());
      list init_declarator_list = NULL;
      qual_type type;
      for(const clang::Decl* singleDecl : declStmt->getDeclGroup())
        {
          assert(llvm::dyn_cast<clang::VarDecl>(singleDecl));
          const clang::VarDecl* varDecl
            = static_cast<const clang::VarDecl*>(singleDecl);
          type
            = makeDefaultType(varDecl->getLocation(), varDecl->getType());
          const char* name = strdup(varDecl->getName().str().c_str());
          if (_implicitThisStar) {
            free_expression(_implicitThisStar);
            _implicitThisStar = NULL;
            _isImplicitThisBare = false;
          };
          if (type->plain_type->tag_typ == STRUCT) {
            location loc = makeLocation(varDecl->getSourceRange());
            variable v
              = variable_Local(_clangUtils->makeQualifiedName(*varDecl));
            expression var = expression_cons(loc,exp_node_Variable(v));
            _implicitThisStar = var;
          };
          /*init_expr*/ option ie = opt_none();
          if (varDecl->hasInit())
            ie =
              opt_some_container(
                makeInitExpr(
                  varDecl->getType(), varDecl->getInit(), shouldDelay));

          if (!_cleanups.empty()) {
            std::cerr << "Unsupported statements to clean the expression\n";
#if CLANG_VERSION_MAJOR >= 11
            forStmt->dump(llvm::errs(), *_context);
#else
            forStmt->dump(llvm::errs(), _context->getSourceManager());
#endif
            std::cerr << "\ncontinue the translation\n";
            _cleanups.clear();
          };
          init_declarator_list = cons_container(
            init_declarator_cons(
              name,
              type,
              ie),
            init_declarator_list);
        }
      init = init_statement_IVarDecl(
        init_declarator_list);
    }
    else if (initClass >= clang::Stmt::firstExprConstant
             && initClass <= clang::Stmt::lastExprConstant) {
      assert(llvm::dyn_cast<clang::Expr>(forStmt->getInit()));
      exp_node initExpr = makeExpression(static_cast<const clang::Expr*>(
                                           forStmt->getInit()), shouldDelay);
      if (!_cleanups.empty()) {
        std::cerr << "Unsupported statements to clean the expression\n";
#if CLANG_VERSION_MAJOR >= 11
        forStmt->dump(llvm::errs(), *_context);
#else
        forStmt->dump(llvm::errs(), _context->getSourceManager());
#endif
        std::cerr << "\ncontinue the translation\n";
        _cleanups.clear();
      };
      expression einitExpr = expression_cons(makeLocation(
                                               forStmt->getInit()->getSourceRange()), initExpr);
      init = init_statement_IExpression(einitExpr);
    }
  };
  /*expression*/ option econdition = NULL;
  if (forStmt->getCond()) {
    exp_node condition = makeExpression(forStmt->getCond(), shouldDelay);
    econdition = opt_some_container
      (expression_cons(makeLocation(forStmt->getCond()->getSourceRange()), condition));
    if (!_cleanups.empty()) {
      std::cerr << "Unsupported statements to clean the expression\n";
#if CLANG_VERSION_MAJOR >= 11
      forStmt->dump(llvm::errs(), *_context);
#else
      forStmt->dump(llvm::errs(), _context->getSourceManager());
#endif
      std::cerr << "\ncontinue the translation\n";
      _cleanups.clear();
    };
  }
  else {
    econdition = opt_none();
  };
  statement body = makeStmt(forStmt->getBody(), NULL, context, shouldDelay);
  incr_statement increment = NULL;
  if (forStmt->getInc()) {
    exp_node incrementExpr = makeExpression(forStmt->getInc(), shouldDelay);
    expression eincrementExpr = expression_cons(makeLocation(
                                                  forStmt->getInc()->getSourceRange()), incrementExpr);
    increment = incr_statement_CExpression(eincrementExpr);
    if (!_cleanups.empty()) {
      if (body->tag_statement != BLOCK)
        body = statement_Block(copy_loc(l), cons_container(body, NULL));
      ForwardReferenceList block(body->cons_statement.Block.instructions);
      /* statement */ list* cursor = block.getBack()
        ? &block.getBack()->next : &block.getFront();
      makeCleanupsStmts(block, cursor, eincrementExpr, context, shouldDelay);
    };
  }
  else
    increment = incr_statement_CNop();
  statement result = statement_For(l,init,econdition,increment,body,NULL);
  _delayedLoopAnnotation.attachTo(forStmt, result);
  if (stmts) {
    forwardStmts.insertContainer(result);
    if (commentLocation) {
      commentLocation = copy_loc(commentLocation);
      extend_location_with(commentLocation, l);
    }
    else
      commentLocation = copy_loc(l);
  };
  return !stmts ? result
    : statement_Block(commentLocation, stmts);
}

statement FramacVisitor::makeLabelStmt(
  const clang::LabelStmt* labelStmt, location l, location commentLocation,
  list& /*<statement>*/stmts, ForwardReferenceList* container,
  ForwardReferenceList& forwardStmts, const clang::DeclContext* context,
  bool* shouldDelay) {
  // implicit precondition: commentLocation != NULL => stmts != NULL
  // the reverse is not true any more thanks to cleanups
  if (container)
    container->insertContainer(statement_Label(l,labelStmt->getName()));
  else
    forwardStmts.insertContainer(statement_Label(l,labelStmt->getName()));
  statement subStatement = makeStmt(labelStmt->getSubStmt(),
      container ? container : &forwardStmts, context, shouldDelay);
  if (!container) {
    forwardStmts.insertContainer(subStatement);
    return statement_Block(l, stmts);
  };
  if (stmts) {
    forwardStmts.insertContainer(subStatement);
    if (commentLocation) {
      commentLocation = copy_loc(commentLocation);
      extend_location_with(commentLocation, l);
      free_location(l);
    }
    else
      commentLocation = l;
  };
  return !stmts ? subStatement : statement_Block(commentLocation, stmts);
}

statement FramacVisitor::makeIfStmt(
  const clang::IfStmt* ifStmt, location l, location commentLocation,
  list& /*<statement>*/stmts, ForwardReferenceList& forwardStmts,
  const clang::DeclContext* context, bool* shouldDelay) {
  // implicit precondition: commentLocation != NULL => stmts != NULL
  // the reverse is not true any more thanks to cleanups
  exp_node condition = makeExpression(ifStmt->getCond(), shouldDelay);
  expression econdition = expression_cons(makeLocation(
      ifStmt->getCond()->getSourceRange()), condition);

  if (!_cleanups.empty()) {
    const char* conditionVarname = mk_tmp_name ();
    forwardStmts.insertContainer(statement_VarDecl(copy_loc(l),
        conditionVarname, qual_type_cons(NULL, typ_Int(IBOOL)), opt_none()));
    /* statement */ list* cursor = forwardStmts.getBack()
      ? &forwardStmts.getBack()->next : &forwardStmts.getFront();
    forwardStmts.insertContainer(statement_Expression(
      copy_loc(econdition->eloc), expression_cons(copy_loc(econdition->eloc),
        exp_node_Assign(
          expression_cons(copy_loc(econdition->eloc), exp_node_Variable(
              variable_Local(qualified_name_cons(NULL,
                strdup(conditionVarname))))),
          econdition))));
    makeCleanupsStmts(forwardStmts, cursor, econdition, context, shouldDelay);
    econdition = expression_cons(copy_loc(econdition->eloc),
      exp_node_Variable(variable_Local(qualified_name_cons(NULL,
        strdup(conditionVarname)))));
  };

  const clang::VarDecl* declared_var = ifStmt->getConditionVariable();
  cond_statement cond = makeCondition(declared_var, econdition,
      shouldDelay);
  statement thenStmt = makeStmt(ifStmt->getThen(), NULL, context,
      shouldDelay);
  const clang::Stmt* cppElseStmt = ifStmt->getElse();
  statement elseStmt = cppElseStmt
    ? makeStmt(ifStmt->getElse(), NULL, context, shouldDelay)
    : statement_Nop(copy_loc(l));
  statement result = statement_Condition(l,cond,thenStmt,elseStmt);
  if (stmts) {
    forwardStmts.insertContainer(result);
    if (commentLocation) {
      commentLocation = copy_loc(commentLocation);
      extend_location_with(commentLocation, l);
    }
    else
      commentLocation = copy_loc(l);
  };
  return !stmts ? result : statement_Block(commentLocation, stmts);
}

statement FramacVisitor::makeSwitchStmt(
  const clang::SwitchStmt* switchStmt, location l, location commentLocation,
  list& /*<statement>*/stmts, ForwardReferenceList& forwardStmts,
  const clang::DeclContext* context, bool* shouldDelay) {
  // implicit precondition: commentLocation != NULL => stmts != NULL
  // the reverse is not true any more thanks to cleanups
  exp_node condition = makeExpression(switchStmt->getCond(), shouldDelay);
  expression econdition = expression_cons(makeLocation(
      switchStmt->getCond()->getSourceRange()), condition);

  if (!_cleanups.empty()) {
    const char* conditionVarname = mk_tmp_name ();
    forwardStmts.insertContainer(statement_VarDecl(copy_loc(l),
        conditionVarname, qual_type_cons(NULL, typ_Int(IBOOL)), opt_none()));
    /* statement */ list* cursor = forwardStmts.getBack()
      ? &forwardStmts.getBack()->next : &forwardStmts.getFront();
    forwardStmts.insertContainer(statement_Expression(
      copy_loc(econdition->eloc), expression_cons(copy_loc(econdition->eloc),
        exp_node_Assign(
          expression_cons(copy_loc(econdition->eloc), exp_node_Variable(
              variable_Local(qualified_name_cons(NULL,
                strdup(conditionVarname))))),
          econdition))));
    makeCleanupsStmts(forwardStmts, cursor, econdition, context, shouldDelay);
    econdition = expression_cons(copy_loc(econdition->eloc),
      exp_node_Variable(variable_Local(qualified_name_cons(NULL,
        strdup(conditionVarname)))));
  };

  const clang::VarDecl* declared_var = switchStmt->getConditionVariable();
  cond_statement cond = makeCondition(declared_var, econdition, shouldDelay);
  std::vector<const clang::SwitchCase*> reverseCaseList;
  const clang::SwitchCase* currentCase = switchStmt->getSwitchCaseList();
  while (currentCase) {
    reverseCaseList.push_back(currentCase);
    currentCase = currentCase->getNextSwitchCase();
  };
  std::vector<const clang::SwitchCase*>::const_reverse_iterator
      caseIterator = reverseCaseList.rbegin();
  std::vector<const clang::SwitchCase*>::const_reverse_iterator
      endCaseIterator = reverseCaseList.rend();

  assert(switchStmt->getBody()->getStmtClass() == clang::Stmt::CompoundStmtClass
      && llvm::dyn_cast<clang::CompoundStmt>(switchStmt->getBody()));
  const clang::CompoundStmt *block
      = static_cast<const clang::CompoundStmt*>(switchStmt->getBody());
  addLabelsInSema(block);
  clang::CompoundStmt::const_body_iterator it = block->body_begin();
  clang::CompoundStmt::const_body_iterator last = block->body_end();
  list /*<case_statement>*/ cases = NULL;
  ForwardReferenceList forwardCases(cases);
  while (caseIterator != endCaseIterator) {
    currentCase = *caseIterator;
    unsigned caseClass = currentCase->getStmtClass();
    assert((caseClass == clang::Stmt::CaseStmtClass)
        || (caseClass == clang::Stmt::DefaultStmtClass));
    case_statement newCase;
    list /*<statement>*/ instructions = NULL;
    ForwardReferenceList forwardInstructions;
    while (*it != currentCase && it != last)
      ++it;
    ++caseIterator;
    const clang::SwitchCase* nextCase = (caseIterator != endCaseIterator)
        ? *caseIterator : NULL;
    if (caseClass == clang::Stmt::CaseStmtClass) {
      compilation_constant cst = makeConstantExpression(
          static_cast<const clang::CaseStmt*>(currentCase)->getLHS());
      newCase = case_statement_Case(cst,instructions);
      forwardInstructions = ForwardReferenceList(newCase->cons_case_statement
          .Case.instructions);
    }
    else { // (caseClass == clang::Stmt::DefaultStmtClass)
      newCase = case_statement_Default(instructions);
      forwardInstructions = ForwardReferenceList(newCase->cons_case_statement
          .Default.instructions);
    };
    forwardCases.insertContainer(newCase);
    if (it != last && *it == currentCase) {
      if (currentCase->getSubStmt()->getStmtClass()
            == clang::Stmt::CaseStmtClass) {
        do {
          assert(currentCase->getSubStmt() == nextCase);
          compilation_constant cst = makeConstantExpression(
              static_cast<const clang::CaseStmt*>(nextCase)->getLHS());
          newCase = case_statement_Case(cst,instructions);
          forwardInstructions = ForwardReferenceList(newCase
              ->cons_case_statement.Case.instructions);
          forwardCases.insertContainer(newCase);
          currentCase = nextCase;
          ++caseIterator;
          nextCase = (caseIterator != endCaseIterator)
              ? *caseIterator : NULL;
        } while (currentCase->getSubStmt()->getStmtClass()
          == clang::Stmt::CaseStmtClass);
      };
      if (currentCase->getSubStmt()->getStmtClass()
            == clang::Stmt::DefaultStmtClass) {
        assert(currentCase->getSubStmt() == nextCase);
        newCase = case_statement_Default(instructions);
        forwardInstructions = ForwardReferenceList(newCase->cons_case_statement
            .Default.instructions);
        forwardCases.insertContainer(newCase);
        currentCase = nextCase;
        ++caseIterator;
        nextCase = (caseIterator != endCaseIterator)
            ? *caseIterator : NULL;
      };
      statement instruction = makeStmt(currentCase->getSubStmt(),
          &forwardInstructions, context, shouldDelay);
      forwardInstructions.insertContainer(instruction);
      ++it;
    };
    if (currentCase != nextCase) {
      while (it != last && *it != nextCase) {
        statement instruction = makeStmt(*it, &forwardInstructions,
            context, shouldDelay);
        forwardInstructions.insertContainer(instruction);
        ++it;
      };
    };
    currentCase = nextCase;
  };
  statement result = statement_Switch(l,cond,cases);
  if (stmts) {
    forwardStmts.insertContainer(result);
    if (commentLocation) {
      commentLocation = copy_loc(commentLocation);
      extend_location_with(commentLocation, l);
    }
    else
      commentLocation = copy_loc(l);
  };
  return !stmts ? result
                : statement_Block(commentLocation, stmts);
}

statement FramacVisitor::makeWhileStmt(
  const clang::WhileStmt* whileStmt, location l, location commentLocation,
  list& /*<statement>*/stmts, ForwardReferenceList& forwardStmts,
  const clang::DeclContext* context, bool* shouldDelay) {
  // implicit precondition: commentLocation != NULL => stmts != NULL
  // the reverse is not true any more thanks to cleanups
  exp_node condition = makeExpression(whileStmt->getCond(), shouldDelay);
  expression econdition = expression_cons(makeLocation(
      whileStmt->getCond()->getSourceRange()), condition);

  const char* conditionVarname = NULL;
  if (!_cleanups.empty()) {
    conditionVarname = mk_tmp_name ();
    forwardStmts.insertContainer(statement_VarDecl(copy_loc(l),
        conditionVarname, qual_type_cons(NULL, typ_Int(IBOOL)), opt_none()));
    /* statement */ list* cursor = forwardStmts.getBack()
      ? &forwardStmts.getBack()->next : &forwardStmts.getFront();
    forwardStmts.insertContainer(statement_Expression(
      copy_loc(econdition->eloc), expression_cons(copy_loc(econdition->eloc),
        exp_node_Assign(
          expression_cons(copy_loc(econdition->eloc), exp_node_Variable(
              variable_Local(qualified_name_cons(NULL,
                strdup(conditionVarname))))),
          expression_dup(econdition)))));
    std::vector<const clang::ExprWithCleanups*> cleanups = _cleanups;
    makeCleanupsStmts(forwardStmts, cursor, econdition, context, shouldDelay);
    cleanups.swap(_cleanups);
  };
  statement body = makeStmt(whileStmt->getBody(),NULL, context, shouldDelay);
  if (!_cleanups.empty()) {
    if (body->tag_statement != BLOCK)
      body = statement_Block(copy_loc(l), cons_container(body, NULL));
    ForwardReferenceList block(body->cons_statement.Block.instructions);
    /* statement */ list* cursor = forwardStmts.getBack()
      ? &forwardStmts.getBack()->next : &forwardStmts.getFront();
    // /* statement */ list* cursor = block.getBack()
    //   ? &block.getBack()->next : &block.getFront();
    block.insertContainer(statement_Expression(
      copy_loc(econdition->eloc), expression_cons(copy_loc(econdition->eloc),
        exp_node_Assign(
          expression_cons(copy_loc(econdition->eloc), exp_node_Variable(
              variable_Local(qualified_name_cons(NULL,
                strdup(conditionVarname))))),
          econdition))));
    makeCleanupsStmts(block, cursor, econdition, context, shouldDelay);
    econdition = expression_cons(copy_loc(econdition->eloc),
      exp_node_Variable(variable_Local(qualified_name_cons(NULL,
        strdup(conditionVarname)))));
  };
  statement result = statement_While(l,econdition,body,NULL);
  _delayedLoopAnnotation.attachTo(whileStmt, result);
  if (stmts) {
    forwardStmts.insertContainer(result);
    if (commentLocation) {
      commentLocation = copy_loc(commentLocation);
      extend_location_with(commentLocation, l);
    }
    else
      commentLocation = copy_loc(l);
  };
  return !stmts ? result
                : statement_Block(commentLocation, stmts);
}

catch_block FramacVisitor::makeCatchBlock(
  const clang::CXXCatchStmt* catchStmt, location l, location commentLocation,
  const clang::DeclContext* context, bool* shouldDelay) {
  // implicit precondition: commentLocation != NULL => stmts != NULL
  // the reverse is not true any more thanks to cleanups
  /* statement */ list stmts = NULL;
  ForwardReferenceList forwardStmts(stmts);
  /* arg_decl */ option declVariable;
  if (catchStmt->getExceptionDecl()) {
    char* name;
    if (catchStmt->getExceptionDecl()->getName().size() > 0)
      name = strdup(catchStmt->getExceptionDecl()->getName().str().c_str());
    else
      name = strdup("__frama_c_arg_except");
    declVariable =
      opt_some_container(
        arg_decl_cons(
          makeDefaultType(
            _clangUtils->getBeginLoc(*catchStmt), catchStmt->getCaughtType()),
          name, makeLocation(catchStmt->getSourceRange())));
  }
  else
    declVariable = opt_none();
  statement block = makeStmt(catchStmt->getHandlerBlock(),
      &forwardStmts, context, shouldDelay);
  if (block->tag_statement == BLOCK) {
    /* statement */ list blockList = block->cons_statement.Block.instructions;
    block->cons_statement.Block.instructions = NULL;
    free_statement(block);
    ForwardReferenceList blockStmts(blockList);
    forwardStmts.append(blockStmts);
  }
  else
    forwardStmts.insertContainer(block);
  return catch_block_cons(declVariable, stmts);
}

statement FramacVisitor::makeTryStmt(
  const clang::CXXTryStmt* tryStmt, location l, location commentLocation,
  list& /*<statement>*/stmts, ForwardReferenceList* container,
  ForwardReferenceList& forwardStmts, const clang::DeclContext* context,
  bool* shouldDelay) {
  // implicit precondition: commentLocation != NULL => stmts != NULL
  // the reverse is not true any more thanks to cleanups
  _parents.pushBlock();
  clang::CompoundStmt::const_body_iterator
      it = tryStmt->getTryBlock()->body_begin(),
      last = tryStmt->getTryBlock()->body_end();
  while(it < last) {
    statement stmt = makeStmt(*it, &forwardStmts, context, shouldDelay);
    forwardStmts.insertContainer(stmt);
    it++;
  }
  _parents.popBlock();
  readStatementCommentUntil(
    _clangUtils->getEndLoc(*tryStmt),
    commentLocation, stmts, forwardStmts, NULL, container, context);
  statement result = statement_TryCatch(l, stmts, NULL);
  /* catch_block */ list* endCatch = &result->cons_statement.TryCatch.cases;
  int numOfCatch = tryStmt->getNumHandlers();
  for (int blockNumber = 0; blockNumber < numOfCatch; ++blockNumber) {
    *endCatch = cons_container(makeCatchBlock(tryStmt->getHandler(blockNumber),
      makeLocation(tryStmt->getHandler(blockNumber)->getSourceRange()),
      commentLocation, context, shouldDelay), NULL);
    endCatch = &(*endCatch)->next;
  };
  return result;
}
statement FramacVisitor::makeGCCAsmStmt(const clang::GCCAsmStmt* asmStmt) {
    location loc = makeLocation(asmStmt->getSourceRange());

    list qualifier = NULL;
    list instructions = NULL;

    if(asmStmt->isVolatile())
        qualifier = cons_plain(VOLATILE, qualifier);

    instructions = cons_container(
                     (void*)strdup(
                       asmStmt->getAsmString()->getString().str().c_str()),
                     instructions);
    asm_IO asm_IO_cons(option aIO_name, const char * constraints, expression
    expr);
    list inputs = NULL;
    list outputs = NULL;
    list clobbers = NULL;
    list labels = NULL;
    bool f = false; // only used because of the API of makeExpression.

    for(int i=asmStmt->getNumInputs()-1; i >= 0; --i)
    {
        std::string name = asmStmt->getInputName(i).str();
        inputs = cons_container(
             asm_IO_cons(
               name.empty() ?
                 opt_none() :
                 opt_some_container((void*) const_cast<char*>(name.c_str())),
               strdup(asmStmt->getInputConstraint(i).str().c_str()),
               expression_cons(
                 copy_loc(loc),
                 makeExpression(asmStmt->getInputExpr(i), &f))),
             inputs);
    }

    for(int i=asmStmt->getNumOutputs()-1; i >= 0; --i)
    {
        std::string name = asmStmt->getOutputName(i).str();
        outputs = cons_container(
              asm_IO_cons(
                name.empty() ?
                  opt_none() :
                  opt_some_container((void*)const_cast<char*>(name.c_str())),
                strdup(asmStmt->getOutputConstraint(i).str().c_str()),
                expression_cons(
                  copy_loc(loc),
                  makeExpression(
                    asmStmt->getOutputExpr(i), &f))),
              outputs);
    }

    assert(!f); // we should not have to delay this definition

    for(unsigned int i=0; i<asmStmt->getNumClobbers(); ++i)
        clobbers = cons_container(
                     (void*)strdup(asmStmt->getClobber(i).str().c_str()),
                     clobbers);

    asm_details details = asm_details_cons(outputs, inputs, clobbers, labels);
    return statement_GccInlineAsm(
             loc,
             qualifier,
             instructions,
             opt_some_container((void*)details));
}

statement FramacVisitor::makeStmt(
  const clang::Stmt* stmt, ForwardReferenceList* container,
  const clang::DeclContext* context, bool* shouldDelay) {
  clang::SourceRange clangRange = stmt->getSourceRange();
  list /*<statement>*/stmts = NULL;
  ForwardReferenceList forwardStmts(stmts);
  
  location commentLocation = NULL;
  // implicit precondition: commentLocation != NULL => stmts != NULL
  // the reverse is not true any more thanks to cleanups
  readStatementCommentUntil(clangRange.getBegin(), commentLocation,
    stmts, forwardStmts, stmt, container, context);

  location l = makeLocation(clangRange);
  clang::Stmt::StmtClass stmtClass = stmt->getStmtClass();
  
  if (stmtClass >= clang::Stmt::firstExprConstant
      && stmtClass <= clang::Stmt::lastExprConstant
      && stmtClass != clang::Stmt::ExprWithCleanupsClass) {
    assert(llvm::dyn_cast<clang::Expr>(stmt));
    exp_node stmtExpr = makeExpression(static_cast<const clang::Expr*>(stmt),
                                       shouldDelay);
    expression estmtExpr = expression_cons(makeLocation(stmt->getSourceRange()),
        stmtExpr);
    if (stmts || !_cleanups.empty()) {
      /* statement */ list* cursor = forwardStmts.getBack()
        ? &forwardStmts.getBack()->next : &forwardStmts.getFront();
      forwardStmts.insertContainer(statement_Expression(l, estmtExpr));
      if (!_cleanups.empty())
        makeCleanupsStmts(forwardStmts,cursor, estmtExpr, context, shouldDelay);
      if (commentLocation) {
        commentLocation = copy_loc(commentLocation);
        extend_location_with(commentLocation, l);
      }
      else
        commentLocation = copy_loc(l);
    };
    return !stmts ? statement_Expression(l, estmtExpr)
                  : statement_Block(commentLocation, stmts);
  };

  switch (stmtClass) {
    case clang::Stmt::ExprWithCleanupsClass:
      assert(llvm::dyn_cast<clang::ExprWithCleanups>(stmt));
      return makeExprWithCleanupsStmt(
          static_cast<const clang::ExprWithCleanups*>(stmt), l, stmts,
          forwardStmts, context, shouldDelay);
    case clang::Stmt::BreakStmtClass:
      if (stmts) {
        forwardStmts.insertContainer(statement_Break(l));
        if (commentLocation) {
          commentLocation = copy_loc(commentLocation);
          extend_location_with(commentLocation, l);
        }
        else
          commentLocation = copy_loc(l);
      };
      return !stmts ? statement_Break(l)
                    : statement_Block(commentLocation, stmts);
    case clang::Stmt::ContinueStmtClass:
      if (stmts) {
        forwardStmts.insertContainer(statement_Continue(l));
        if (commentLocation) {
          commentLocation = copy_loc(commentLocation);
          extend_location_with(commentLocation, l);
        }
        else
          commentLocation = copy_loc(l);
      };
      return !stmts ? statement_Continue(l)
                    : statement_Block(commentLocation, stmts);
    case clang::Stmt::CompoundStmtClass:
      assert(llvm::dyn_cast<clang::CompoundStmt>(stmt));
      return makeCompoundStmt(
          static_cast<const clang::CompoundStmt*>(stmt), l, commentLocation,
          stmts, container, forwardStmts, context, shouldDelay);
    case clang::Stmt::ReturnStmtClass:
      assert(llvm::dyn_cast<clang::ReturnStmt>(stmt));
      return makeReturnStmt(static_cast<const clang::ReturnStmt*>(stmt),
          l, commentLocation, stmts, forwardStmts, context, shouldDelay);
    case clang::Stmt::DeclStmtClass:
      assert(llvm::dyn_cast<clang::DeclStmt>(stmt));
      return makeDeclStmt(static_cast<const clang::DeclStmt*>(stmt),
          l, commentLocation, stmts, container, forwardStmts, context,
          shouldDelay);
    case clang::Stmt::CXXDefaultArgExprClass:
      { assert(llvm::dyn_cast<clang::Expr>(stmt));
        exp_node stmtExpr = makeExpression(
          static_cast<const clang::Expr*>(stmt), shouldDelay);
        expression estmtExpr
            = expression_cons(makeLocation(stmt->getSourceRange()), stmtExpr);
        if (stmts || !_cleanups.empty()) {
          /* statement */ list* cursor = forwardStmts.getBack()
            ? &forwardStmts.getBack()->next : &forwardStmts.getFront();
          forwardStmts.insertContainer(statement_Expression(l, estmtExpr));
          if (!_cleanups.empty())
            makeCleanupsStmts(forwardStmts, cursor, estmtExpr, context,
              shouldDelay);
          if (commentLocation) {
            commentLocation = copy_loc(commentLocation);
            extend_location_with(commentLocation, l);
          }
          else
            commentLocation = copy_loc(l);
        };
        return !stmts ? statement_Expression(l, estmtExpr)
                      : statement_Block(commentLocation, stmts);
      };
    case clang::Stmt::DoStmtClass:
      assert(llvm::dyn_cast<clang::DoStmt>(stmt));
      return makeDoStmt(static_cast<const clang::DoStmt*>(stmt),
          l, commentLocation, stmts, forwardStmts, context, shouldDelay);
    case clang::Stmt::ForStmtClass:
      assert(llvm::dyn_cast<clang::ForStmt>(stmt));
      return makeForStmt(static_cast<const clang::ForStmt*>(stmt),
          l, commentLocation, stmts, forwardStmts, context, shouldDelay);
    case clang::Stmt::LabelStmtClass:
      assert(llvm::dyn_cast<clang::LabelStmt>(stmt));
      return makeLabelStmt(static_cast<const clang::LabelStmt*>(stmt), l,
        commentLocation, stmts, container, forwardStmts, context, shouldDelay);
    case clang::Stmt::GotoStmtClass:
      { assert(llvm::dyn_cast<clang::GotoStmt>(stmt));
        const clang::GotoStmt* gotoStmt
            = static_cast<const clang::GotoStmt*>(stmt);
        statement result = statement_Goto(l, strdup(
            gotoStmt->getLabel()->getName().str().c_str()));
        if (stmts) {
          forwardStmts.insertContainer(result);
          if (commentLocation) {
            commentLocation = copy_loc(commentLocation);
            extend_location_with(commentLocation, l);
          }
          else
            commentLocation = copy_loc(l);
        };
        return !stmts ? result
                      : statement_Block(commentLocation, stmts);
      }
    case clang::Stmt::IfStmtClass:
      assert(llvm::dyn_cast<clang::IfStmt>(stmt));
      return makeIfStmt(static_cast<const clang::IfStmt*>(stmt),
          l, commentLocation, stmts, forwardStmts, context, shouldDelay);
    case clang::Stmt::SwitchStmtClass:
      assert(llvm::dyn_cast<clang::SwitchStmt>(stmt));
      return makeSwitchStmt(static_cast<const clang::SwitchStmt*>(stmt),
          l, commentLocation, stmts, forwardStmts, context, shouldDelay);
    case clang::Stmt::WhileStmtClass:
      assert(llvm::dyn_cast<clang::WhileStmt>(stmt));
      return makeWhileStmt(static_cast<const clang::WhileStmt*>(stmt),
          l, commentLocation, stmts, forwardStmts, context, shouldDelay);
    
    case clang::Stmt::ParenExprClass: {
      const clang::ParenExpr* pe = llvm::dyn_cast<const clang::ParenExpr>(stmt);
      assert(pe);
      return makeStmt(pe->getSubExpr(), container, context , shouldDelay);
    }

    case clang::Stmt::NullStmtClass:
      if (stmts) {
        if (commentLocation) {
          commentLocation = copy_loc(commentLocation);
          extend_location_with(commentLocation, l);
          free_location(l);
        }
        else
          commentLocation = l;
      };
      return !stmts ? statement_Nop(l)
                    : statement_Block(commentLocation, stmts);
    case clang::Stmt::CXXTryStmtClass:
      assert(llvm::dyn_cast<clang::CXXTryStmt>(stmt));
      return makeTryStmt(static_cast<const clang::CXXTryStmt*>(stmt), l,
        commentLocation, stmts, container, forwardStmts, context, shouldDelay);
    case clang::Stmt::CXXCatchStmtClass:
      assert(false);
      std::cerr << "Unsupported direct catch:\n";
#if CLANG_VERSION_MAJOR >= 11
      stmt->dump(llvm::errs(), *_context);
#else
      stmt->dump(llvm::errs(), _context->getSourceManager());
#endif
      std::cerr << "\nAborting\n";
      exit(2);

    case clang::Stmt::GCCAsmStmtClass:
      assert(llvm::dyn_cast<clang::GCCAsmStmt>(stmt));
      return makeGCCAsmStmt(static_cast<const clang::GCCAsmStmt*>(stmt));

    case clang::Stmt::MSAsmStmtClass:
    case clang::Stmt::AttributedStmtClass:
    case clang::Stmt::CXXForRangeStmtClass:
    case clang::Stmt::IndirectGotoStmtClass:
    case clang::Stmt::MSDependentExistsStmtClass:
    default:
      std::cerr << "Unsupported Statement:\n";
#if CLANG_VERSION_MAJOR >= 11
      stmt->dump(llvm::errs(), *_context);
#else
      stmt->dump(llvm::errs(), _context->getSourceManager());
#endif
      std::cerr << "\nAborting\n";
      exit(2);
  }
}

list /*<statement>*/ FramacVisitor::makeCodeBlock(
  const clang::Stmt* body, const clang::DeclContext* context,
  const clang::FunctionDecl* Decl, bool* shouldDelay) {
  list /*<statement>*/stmts = NULL;
  ForwardReferenceList forwardStmts(stmts);
  switch (body->getStmtClass()) {
    case clang::Stmt::CompoundStmtClass:
      { const clang::CompoundStmt *block
            = static_cast<const clang::CompoundStmt *>(body);
        addLabelsInSema(block);
        clang::CompoundStmt::const_body_iterator it = block->body_begin();
        clang::CompoundStmt::const_body_iterator last = block -> body_end();
        while(it < last) {
          statement stmt = makeStmt(*it, &forwardStmts, context, shouldDelay);
          forwardStmts.insertContainer(stmt);
          it++;
        }
        break;
      }
    default:
      { statement single = makeStmt(body, &forwardStmts, context, shouldDelay);
        forwardStmts.insertContainer(single);
        break;
      }
  }

  location commentLocation = NULL;
  readStatementCommentUntil(Decl->getSourceRange().getEnd(),
    commentLocation, stmts, forwardStmts, NULL, NULL, context);
  if (commentLocation)
    free_location(commentLocation);
  return stmts;
}

void FramacVisitor::ensureVaListDeclaration(const clang::RecordDecl* decl) {
  if (!_generatedVaList) {
    _generatedVaList = true;
    tkind templateParameters = NULL;
    const char* name = _clangUtils->get_aggregate_name(decl, &templateParameters);
    location loc = makeLocation(decl->getSourceRange());
    ckind type;
    switch (decl->getTagKind()) {
      case clang::TTK_Struct:
        type = CSTRUCT;
        break;
      case clang::TTK_Class:
        type = CCLASS;
        break;
      case clang::TTK_Union:
        type = CUNION;
        break;
      default:
        std::cerr << "Unsupported Record Declaration:"
            << name
            << "\nAborting\n";
        exit(2);
    };
    /* inheritance list */ option inherits = opt_none();
    decl_or_impl_name decl_name = decl_or_impl_name_Declaration(name);
    translation_unit_decl compound = translation_unit_decl_Compound(loc,
        decl_name, type, inherits, opt_some_container(NULL), false,
        templateParameters, Clang_utils::isExternCContext(decl),_ghost);
    _globals.insertBeforeContainer(compound);
    ForwardReferenceList content(*(/* class_decl */ list*)
        &((option) compound->cons_translation_unit_decl.Compound.body)
           ->content.container);
    clang::RecordDecl::decl_iterator
      declIterEnd = decl->decls_end(), declIter = decl->decls_begin();
    for (; declIter != declIterEnd; ++declIter) {
      clang::Decl* Child = *declIter;
      clang::Decl::Kind kind = Child->getKind();
      if (kind == clang::Decl::Field) {
        const clang::FieldDecl* fieldDecl = (const clang::FieldDecl*) Child;
        const char* name = _clangUtils->get_field_name(fieldDecl);
        location loc = makeLocation(fieldDecl->getSourceRange());
        clang::QualType type = fieldDecl->getType();
        qual_type declarationType;
        declarationType = makeDefaultType(fieldDecl->getLocation(), type);
        class_decl decl =
          class_decl_CFieldDecl(
            loc, name, declarationType, opt_none(), fieldDecl->isMutable());
        content.insertContainer(decl);
      }
      else if (kind >= clang::Decl::firstFunction
          && kind <= clang::Decl::lastFunction) {
        auto functionDecl = (const clang::FunctionDecl*) Child;
        if (!functionDecl->isDeleted()) {
          const char* name = copy_string(functionDecl->getNameAsString ());
          tkind templateExtension = tkind_TStandard();
          location loc = makeLocation(functionDecl->getSourceRange());
          qual_type return_type =
	    makeDefaultExternalNameType(
	    functionDecl->getLocation(),
            functionDecl->getReturnType());
          list /*arg_decl*/ prms = NULL;
          for (int i = functionDecl->getNumParams() - 1;i>=0;i--) {
            arg_decl cdecl = (arg_decl)malloc(sizeof(*cdecl));
            prms = cons_container(cdecl,prms);
            const clang::ParmVarDecl *prm = functionDecl->getParamDecl(i);
            if (prm->getNameAsString().size() > 0)
              cdecl->arg_name = copy_string(prm->getNameAsString());
            else {
              std::ostringstream out;
              out << "__frama_c_arg_" << i;
              cdecl->arg_name = copy_string(out.str());
            };
            cdecl->arg_type =
              makeDefaultExternalNameType(
                prm->getLocation(), prm->getOriginalType());
            cdecl->arg_loc = makeLocation(prm->getSourceRange());
          }

          // Body
          option /*statement*/ body = opt_none();
          bool isImplicitFunction = false;
          if (functionDecl->isThisDeclarationADefinition()) {
            if (clang::CXXMethodDecl::classof(functionDecl)) {
              const clang::CXXMethodDecl* meth
                = static_cast<const clang::CXXMethodDecl*>(functionDecl);
              if (_clangUtils->doesGenerateImplicitMethods()
                  || meth->isUserProvided()) {
                list /*<statement>*/ funContent = makeCodeBlock(
                  functionDecl->getBody(),
                  functionDecl->getDeclContext(), functionDecl);
                free(body);
                body = opt_some_container(funContent);
              }
              else
                isImplicitFunction = true;
            }
            else {
              list /*<statement>*/ funContent = makeCodeBlock(
                functionDecl->getBody(),
                functionDecl->getDeclContext(), functionDecl);
              free(body);
              body = opt_some_container(funContent);
            };
          };

          const clang::RecordDecl* current_class = decl;
          funkind kind;
          if (functionDecl->getCanonicalDecl()->getStorageClass()
              == clang::SC_Static)
            kind = funkind_FKFunction();
          else {
            const auto meth =
              llvm::cast<const clang::CXXMethodDecl>(functionDecl);
            if (clang::CXXMethodDecl::classof(functionDecl)) {
            };
            arg_decl cdecl = (arg_decl)malloc(sizeof(*cdecl));
            prms = cons_container(cdecl,prms);
            cdecl->arg_name = copy_string("this");
            clang::QualType typeClass(current_class->getTypeForDecl(), 0);
            qual_type this_type =
              _clangUtils->makeType(functionDecl->getLocation(), typeClass);
            this_type->qualifier = cv_this_ptr(meth);
            pkind pointerKind = pkind_PDataPointer(this_type);
            cdecl->arg_type = qual_type_cons(NULL, typ_Pointer(pointerKind));
            cdecl->arg_loc = makeLocation(functionDecl->getSourceRange());
            if (llvm::isa<clang::CXXConstructorDecl>(meth)) {
              kind = funkind_FKConstructor(true);
              if (strlen(name) == 0) {
                free(const_cast<char*>(name));
                name = strdup("constructor-special");
              }
              if (body->is_some) {
                list& contentBody = *(list*)&body->content.container;
                insertConstructorPreambleIn(
                  *llvm::cast<const clang::CXXConstructorDecl>(meth),
                  contentBody,NULL);
              }
            } else if (llvm::isa<clang::CXXDestructorDecl>(meth)) {
              kind = funkind_FKDestructor(true);
              if (body->is_some)
                insertDestructorPreambleIn(
                *llvm::cast<const clang::CXXDestructorDecl>(meth), body);
            } else {
              kind = _clangUtils->cv_meth(meth);
            }
          }
          bool is_implicit = isImplicitFunction || functionDecl->isDefaulted();
          bool is_variadic = functionDecl->isVariadic();
          class_decl method = class_decl_CMethod(
            loc, name, kind, return_type,
            prms, is_variadic, body, is_implicit, templateExtension,
            false /* has_further_definition */,
            opt_none() /* throws */,
            opt_none() /* contract */);
          content.insertContainer(method);
        };
      }
    }
    _tableForWaitingDeclarations.addDeclaration(decl, _globals);
  }
}

void FramacVisitor::insertNamedDeclaration(
  const clang::Decl* decl, bool isBefore) {
  clang::Decl::Kind kindDecl = decl->getKind();
  if (kindDecl >= clang::Decl::firstNamed && kindDecl <= clang::Decl::lastNamed)
  { assert(llvm::dyn_cast<clang::NamedDecl>(decl));
    qualified_name name = _clangUtils->makeQualifiedName(
        *static_cast<const clang::NamedDecl*>(decl));
    decl_or_impl_name decl_name = decl_or_impl_name_Implementation(name);
    translation_unit_decl resultDecl = NULL;
    if (kindDecl >= clang::Decl::firstRecord
        && kindDecl <= clang::Decl::lastRecord) {
      assert(llvm::dyn_cast<clang::RecordDecl>(decl));
      const clang::RecordDecl* recordDecl
          = static_cast<const clang::RecordDecl*>(decl);
      location loc = makeLocation(recordDecl->getSourceRange());
      switch (recordDecl->getTagKind()) {
        case clang::TTK_Struct:
          free(const_cast<char*>(name->decl_name));
          { tkind templateParameters = NULL;
            name->decl_name = _clangUtils->get_aggregate_name(recordDecl,
                &templateParameters);
            if (!_generatedVaList && !recordDecl->isFromASTFile()
                && strcmp(name->decl_name, "__va_list_tag") == 0)
              ensureVaListDeclaration(recordDecl);
            resultDecl =
              translation_unit_decl_Compound(
                loc, decl_name, CSTRUCT, opt_none(), opt_none(),
                false, templateParameters,
                Clang_utils::isExternCContext(recordDecl),
                false /* ghost */);
          };
          break;
        case clang::TTK_Class:
          free(const_cast<char*>(name->decl_name));
          { tkind templateParameters = NULL;
            name->decl_name = _clangUtils->get_aggregate_name(recordDecl,
                &templateParameters);
            resultDecl =
              translation_unit_decl_Compound(
                loc, decl_name, CCLASS, opt_none(), opt_none(),
                false, templateParameters,
                Clang_utils::isExternCContext(recordDecl), _ghost);
          };
          break;
        case clang::TTK_Union:
          free(const_cast<char*>(name->decl_name));
          { tkind templateParameters = NULL;
            name->decl_name = _clangUtils->get_aggregate_name(recordDecl,
                &templateParameters);
            resultDecl =
              translation_unit_decl_Compound(
                loc, decl_name, CUNION, opt_none(), opt_none(), false,
                templateParameters, Clang_utils::isExternCContext(recordDecl),
                _ghost);
          };
          break;
        case clang::TTK_Enum:
          resultDecl =
            translation_unit_decl_EnumDecl(
              loc, decl_name, IINT,
              /* compilation_constant list option */ opt_none(),
              Clang_utils::isExternCContext(recordDecl),
              _ghost);
          break;
        default:
          free_location(loc);
          break;
      };
    }
    else if (kindDecl >= clang::Decl::firstType
        && kindDecl <= clang::Decl::lastType) {
      location loc = makeLocation(decl->getSourceRange());
      if (kindDecl == clang::Decl::Enum)
        resultDecl =
          translation_unit_decl_EnumDecl(
            loc, decl_name, IINT,
            /* compilation_constant list option */ opt_none(),
            Clang_utils::isExternCContext(decl->getDeclContext()), _ghost);
      else if (kindDecl == clang::Decl::Typedef) {
        const clang::TypedefDecl* typedefDecl=(const clang::TypedefDecl*) decl;
        if (_generatedTypedefsInAdvance.find(typedefDecl)
            == _generatedTypedefsInAdvance.end()) {
          qual_type targetType =
            makeDefaultExternalNameType(
              typedefDecl->getLocation(), typedefDecl->getUnderlyingType());
          resultDecl =
            translation_unit_decl_Typedef(
              loc, decl_name, targetType, false, _ghost);
          _generatedTypedefsInAdvance.insert(typedefDecl);
        };
        // mainly for __va_list_tag;
        // resultDecl = translation_unit_decl_Typename(loc, name);
      }
      else {
         decl_or_impl_name decl_name = decl_or_impl_name_Implementation(name);
         resultDecl =
           translation_unit_decl_Compound(
             loc, decl_name, CCLASS,
             opt_none(), opt_none(), false, tkind_TStandard(), false, _ghost);
         assert(false);
      };
    }
    if (resultDecl) {
      if (isBefore)
         _globals.insertBeforeContainer(resultDecl);
      else
         _globals.insertContainer(resultDecl);
    }
    else
      free_decl_or_impl_name(decl_name);
  };
}

qual_type FramacVisitor::makeDefaultType(
  clang::SourceLocation const& loc, clang::QualType const& type)
{ qual_type result;
  if (hasInstanceContext()) {
    FramaCIRGenAction::UnvisitedRegistration unvisitedRegistration(*this);
    result = _clangUtils->makeType(loc, type, &unvisitedRegistration);
  }
  else {
    FramaCIRGenAction::VerifyNameRegistration insertMissingDeclRegistration(
        const_cast<FramacVisitor&>(*this));
    result = _clangUtils->makeType(loc, type, &insertMissingDeclRegistration);
  };
  return result;
}

qual_type FramacVisitor::makeDefaultNameType(
  clang::SourceLocation const& loc, clang::QualType const& type)
{ qual_type result;
  if (hasInstanceContext()) {
    FramaCIRGenAction::UnvisitedNameRegistration unvisitedRegistration(*this);
    result = _clangUtils->makeType(loc, type, &unvisitedRegistration);
  }
  else {
    FramaCIRGenAction::VerifyNameRegistration insertMissingDeclRegistration(
        const_cast<FramacVisitor&>(*this));
    result = _clangUtils->makeType(loc, type, &insertMissingDeclRegistration);
  };
  return result;
}

qual_type FramacVisitor::makeDefaultExternalNameType(
    clang::SourceLocation const& loc, clang::QualType const& type)
{ qual_type result;
  if (hasInstanceContext()) {
    FramaCIRGenAction::UnvisitedNameRegistration unvisitedRegistration(
        const_cast<FramacVisitor&>(*this));
    unvisitedRegistration.setExternal();
    result = _clangUtils->makeType(loc, type, &unvisitedRegistration);
  }
  else {
    FramaCIRGenAction::VerifyNameRegistration
      insertMissingDeclRegistration(*this);
    result = _clangUtils->makeType(loc, type, &insertMissingDeclRegistration);
  };
  return result;
}

bool
FramaCIRGenAction::isAtTopNamespace(const clang::DeclContext* ctx) {
  while(ctx && ctx->getDeclKind()==clang::Decl::Namespace)
    ctx = ctx->getParent();
  if (ctx->getDeclKind()==clang::Decl::LinkageSpec) {
    const clang::LinkageSpecDecl* link_ctx
      = static_cast<const clang::LinkageSpecDecl*>(ctx);
    return link_ctx->getLanguage() == clang::LinkageSpecDecl::lang_c;
  }
  return !ctx->getParent();
}

int FramacVisitor::findCommentAfterRange(clang::SourceRange range) {
  int result = (int) _annotationCommentList.size()-1;
  AnnotationComment commentLocation(range);
  clang::BeforeThanCompare<AnnotationComment> Compare(
      _context->getSourceManager());
  AnnotationCommentList::iterator found = std::lower_bound(
      _annotationCommentList.begin(), _annotationCommentList.end(),
      &commentLocation, Compare);
  if (found != _annotationCommentList.end())
    result = &*found - &*_annotationCommentList.begin();
  return result;
}

void FramacVisitor::advanceCommentUntil(clang::SourceLocation sourceLocation) {
  if (_templateCommentIndex < -1) {
    while ((_commentIndex < (int) _annotationCommentList.size()-1)
        && _context->getSourceManager().isBeforeInTranslationUnit(
            _annotationCommentList[_commentIndex+1]->getSourceRange().getEnd(),
            sourceLocation))
      ++_commentIndex;
  }
  else {
    while ((_templateCommentIndex < (int) _annotationCommentList.size()-1)
      && _context->getSourceManager().isBeforeInTranslationUnit(
        _annotationCommentList[_templateCommentIndex+1]
          ->getSourceRange().getEnd(), sourceLocation))
      ++_templateCommentIndex;
  };
}

inline void FramacVisitor::parseGhostGlobal(
  AnnotationComment& comment,
  clang::DeclContext* clangContext) {
  _ghost = true;
  comment.parseGhostGlobal(
    clangContext,
    _sema,
    _parents.getScope(),
    _commentHandler.compilerInstance(),
    this);
  _ghost = false;
}

void FramacVisitor::parseGlobalComment(
  AnnotationComment& comment, const clang::DeclContext* clangContext) {
  location loc = makeLocation(comment.getSourceRange());
  loc->charnum1 += 3;
  if (comment.isLineComment())
    loc->charnum2 -= 1;
  else
    loc->charnum2 -= 3;
  ForwardReferenceList& container =
    _parents.isNamespace()?_parents.getNamespaceContent():_globals;
  comment.parseGlobal(
    container, _parents.isClass() ? &_parents.getClassContent() : NULL,
    clangContext, _context, _sema, _parents.getScope(),
    _clangUtils, _rttiTable, loc);
}

void FramacVisitor::parseGhostStatement(
  AnnotationComment& comment,
  const clang::DeclContext* clangContext,
  ForwardReferenceList* container) {
  std::cerr << "Ghost code is not supported yet" << std::endl;
  if (_clangUtils->stopOnAnnotError()) exit(2);
  else std::cerr << "Ignoring code" << std::endl;
}

void FramacVisitor::parseCodeAnnotation(
  AnnotationComment& comment,
  const clang::DeclContext* clangContext, ForwardReferenceList* container) {
  const clang::SourceLocation& clang_loc = comment.getSourceLocation();
  location loc = makeLocation(clang_loc);
  loc->charnum1 += 3;
  if (comment.isLineComment())
    loc->charnum2 -= 1;
  else
    loc->charnum2 -= 3;

  comment.parseCodeAnnotation(*container, clangContext, _context, _sema,
      _parents.getScope(), _clangUtils, _rttiTable, loc);
}

void FramacVisitor::addLocalVariablesInSema(
    const clang::DeclStmt * declStmt, clang::Scope* scope) {
  clang::DeclStmt::const_decl_iterator iter_end = declStmt->decl_end();
  for (clang::DeclStmt::const_decl_iterator
      iter = declStmt->decl_begin(); iter != iter_end; ++iter) {
    clang::Decl* singleDecl = *iter;
    clang::Decl::Kind kind = singleDecl->getKind();
    if (kind >= clang::Decl::firstNamed
        && kind <= clang::Decl::lastNamed) {
      assert(llvm::dyn_cast<clang::NamedDecl>(singleDecl));
      clang::NamedDecl* decl = static_cast<clang::NamedDecl*>(singleDecl);
      if (decl->getName().size() > 0)
        _sema->PushOnScopeChains(decl, scope, false);
      else
        scope->AddDecl(decl);
    }
    else
      scope->AddDecl(singleDecl);
  };
}

void FramacVisitor::addLocalVariablesInSema(
    const clang::CompoundStmt * block, clang::Scope* scope) {
  clang::CompoundStmt::const_body_iterator it = block->body_begin();
  clang::CompoundStmt::const_body_iterator last = block->body_end();
  while (it < last) {
    const clang::Stmt* stmt = *it;
    while (stmt->getStmtClass() == clang::Stmt::LabelStmtClass) {
      assert(llvm::dyn_cast<clang::LabelStmt>(stmt));
      const clang::LabelStmt* labelStmt
          = static_cast<const clang::LabelStmt*>(stmt);
      stmt = labelStmt->getSubStmt();
      clang::LabelDecl* decl = labelStmt->getDecl();
      if (decl->getName().size() > 0)
        _sema->PushOnScopeChains(decl, scope, false);
      else
        scope->AddDecl(decl);
    };
    
    if (stmt->getStmtClass() == clang::Stmt::DeclStmtClass) {
      assert(llvm::dyn_cast<clang::DeclStmt>(stmt));
      addLocalVariablesInSema(static_cast<const clang::DeclStmt*>(stmt), scope);
    };
    it++;
  }
}

void FramacVisitor::addLabelsInSema(const clang::CompoundStmt * block) {
  clang::CompoundStmt::const_body_iterator it = block->body_begin();
  clang::CompoundStmt::const_body_iterator last = block->body_end();
  while (it < last) {
    const clang::Stmt* stmt = *it;
    while (stmt->getStmtClass() == clang::Stmt::LabelStmtClass) {
      assert(llvm::dyn_cast<clang::LabelStmt>(stmt));
      const clang::LabelStmt* labelStmt
          = static_cast<const clang::LabelStmt*>(stmt);
      stmt = labelStmt->getSubStmt();
      _parents.addDecl(labelStmt->getDecl());
    };
    it++;
  }
}

void FramacVisitor::parseLoopAnnotation(
  AnnotationComment& comment, const clang::Stmt* stmt,
  const clang::DeclContext* clangContext, ForwardReferenceList* container) {
  const clang::SourceLocation& clang_loc = comment.getSourceLocation();
  location loc = makeLocation(clang_loc);
  loc->charnum1 += 3;
  if (comment.isLineComment())
    loc->charnum2 -= 1;
  else
    loc->charnum2 -= 3;

  const clang::CompoundStmt * foundBlock = NULL;
  clang::Scope* originalScope = _parents.getScope();
  clang::Scope* scope = originalScope;
  const clang::Stmt* foundLoop = NULL;

LAddSema:
  switch (stmt->getStmtClass()) {
    case clang::Stmt::DoStmtClass:
      { assert(llvm::dyn_cast<clang::DoStmt>(stmt));
        foundLoop = stmt;
        const clang::DoStmt* doStmt = static_cast<const clang::DoStmt*>(stmt);
        if (doStmt->getBody()->getStmtClass() == clang::Stmt::CompoundStmtClass)
        { assert(llvm::dyn_cast<clang::CompoundStmt>(doStmt->getBody()));
          foundBlock = static_cast<const clang::CompoundStmt*>(
              doStmt->getBody());
        };
      };
      break;
    case clang::Stmt::ForStmtClass:
      { assert(llvm::dyn_cast<clang::ForStmt>(stmt));
        foundLoop = stmt;
        const clang::ForStmt* forStmt= static_cast<const clang::ForStmt*>(stmt);
        if (forStmt->getInit()) {
          clang::Stmt::StmtClass initClass = forStmt->getInit()->getStmtClass();
          if (initClass == clang::Stmt::DeclStmtClass) {
            assert(llvm::dyn_cast<clang::DeclStmt>(forStmt->getInit()));
            scope = new clang::Scope(originalScope, 0, getDiagnosticEngine());
            pushCompoundScope();
            addLocalVariablesInSema(static_cast<const clang::DeclStmt*>(
                  forStmt->getInit()), scope);
          };
        };
        if (forStmt->getBody()->getStmtClass()==clang::Stmt::CompoundStmtClass)
        { assert(llvm::dyn_cast<clang::CompoundStmt>(forStmt->getBody()));
          foundBlock = static_cast<const clang::CompoundStmt*>(
              forStmt->getBody());
        };
      };
      break;
    case clang::Stmt::LabelStmtClass:
      { assert(llvm::dyn_cast<clang::LabelStmt>(stmt));
        const clang::LabelStmt* labelStmt
            = static_cast<const clang::LabelStmt*>(stmt);
        stmt = labelStmt->getSubStmt();
      };
      goto LAddSema;
    case clang::Stmt::WhileStmtClass:
      { assert(llvm::dyn_cast<clang::WhileStmt>(stmt));
        foundLoop = stmt;
        const clang::WhileStmt* whileStmt
            = static_cast<const clang::WhileStmt*>(stmt);
        if (whileStmt->getBody()->getStmtClass()
            == clang::Stmt::CompoundStmtClass)
        { assert(llvm::dyn_cast<clang::CompoundStmt>(whileStmt->getBody()));
          foundBlock = static_cast<const clang::CompoundStmt*>(
              whileStmt->getBody());
        };
      };
    default:
      break;
  }

  clang::Scope* parentLoopBody = scope;
  if (foundBlock) {
    scope = new clang::Scope(scope, 0, getDiagnosticEngine());
    pushCompoundScope();
    addLocalVariablesInSema(foundBlock, scope);
  };

  /* statement */ list result = comment.parseLoopAnnotation(clangContext,
      _context, _sema, scope, _clangUtils, _rttiTable, loc);
  if (foundLoop) {
    /* code_annotation */ list delayedResult = NULL;
    /* code_annotation */ list* backDelayedResult = &delayedResult;
    while (result) {
      statement annotStmt = (statement) result->element.container;
      assert(annotStmt->tag_statement == CODE_ANNOT);
      *backDelayedResult = cons_container(annotStmt->cons_statement.Code_annot
          .body, NULL);
      backDelayedResult = &(*backDelayedResult)->next;
      annotStmt->cons_statement.Code_annot.body = NULL;
      free_location(annotStmt->cons_statement.Code_annot.loc);
      annotStmt->cons_statement.Code_annot.loc = NULL;
      free(annotStmt);
      result->element.container = NULL;
      /* statement */ list temp = result;
      result = result->next;
      free(temp);
    };
    _delayedLoopAnnotation.setAnnotation(foundLoop, delayedResult);
  }
  else {
    ForwardReferenceList annotStmts(result);
    container->append(annotStmts);
  };

  if (foundBlock) {
    _sema->PopCompoundScope();
    delete scope;
    scope = parentLoopBody;
  };
  if (scope != originalScope) {
    _sema->PopCompoundScope();
    delete scope;
    // scope = originalScope;
  };
}

void FramacVisitor::parseStatementAnnotation(
  AnnotationComment& comment, const clang::Stmt* stmt,
  const clang::DeclContext* clangContext, ForwardReferenceList* container) {
  const clang::SourceLocation& clang_loc = comment.getSourceLocation();
  location loc = makeLocation(clang_loc);
  loc->charnum1 += 3;
  if (comment.isLineComment())
    loc->charnum2 -= 1;
  else
    loc->charnum2 -= 3;

  const clang::CompoundStmt * foundBlock = NULL;
  const clang::DeclStmt * foundDecl = NULL;
  clang::Scope* originalScope = _parents.getScope();
  clang::Scope* scope = originalScope;

LAddSema:
  switch (stmt->getStmtClass()) {
    case clang::Stmt::CompoundStmtClass:
      { assert(llvm::dyn_cast<clang::CompoundStmt>(stmt));
        foundBlock = static_cast<const clang::CompoundStmt*>(stmt);
      }
      break;
    case clang::Stmt::DeclStmtClass:
      { assert(llvm::dyn_cast<clang::DeclStmt>(stmt));
        foundDecl = static_cast<const clang::DeclStmt*>(stmt);
      };
      break;
    case clang::Stmt::DoStmtClass:
      { assert(llvm::dyn_cast<clang::DoStmt>(stmt));
        const clang::DoStmt* doStmt = static_cast<const clang::DoStmt*>(stmt);
        if (doStmt->getBody()->getStmtClass() == clang::Stmt::CompoundStmtClass)
        { assert(llvm::dyn_cast<clang::CompoundStmt>(doStmt->getBody()));
          foundBlock = static_cast<const clang::CompoundStmt*>(
              doStmt->getBody());
        };
      };
      break;
    case clang::Stmt::ForStmtClass:
      { assert(llvm::dyn_cast<clang::ForStmt>(stmt));
        const clang::ForStmt* forStmt= static_cast<const clang::ForStmt*>(stmt);
        if (forStmt->getInit()) {
          clang::Stmt::StmtClass initClass = forStmt->getInit()->getStmtClass();
          if (initClass == clang::Stmt::DeclStmtClass) {
            assert(llvm::dyn_cast<clang::DeclStmt>(forStmt->getInit()));
            scope = new clang::Scope(originalScope, 0, getDiagnosticEngine());
            pushCompoundScope();
            addLocalVariablesInSema(static_cast<const clang::DeclStmt*>(
                  forStmt->getInit()), scope);
          };
        };
        if (forStmt->getBody()->getStmtClass()==clang::Stmt::CompoundStmtClass)
        { assert(llvm::dyn_cast<clang::CompoundStmt>(forStmt->getBody()));
          foundBlock = static_cast<const clang::CompoundStmt*>(
              forStmt->getBody());
        };
      };
      break;
    case clang::Stmt::LabelStmtClass:
      { assert(llvm::dyn_cast<clang::LabelStmt>(stmt));
        const clang::LabelStmt* labelStmt
            = static_cast<const clang::LabelStmt*>(stmt);
        stmt = labelStmt->getSubStmt();
      };
      goto LAddSema;
    case clang::Stmt::WhileStmtClass:
      { assert(llvm::dyn_cast<clang::WhileStmt>(stmt));
        const clang::WhileStmt* whileStmt
            = static_cast<const clang::WhileStmt*>(stmt);
        if (whileStmt->getBody()->getStmtClass()
            == clang::Stmt::CompoundStmtClass)
        { assert(llvm::dyn_cast<clang::CompoundStmt>(whileStmt->getBody()));
          foundBlock = static_cast<const clang::CompoundStmt*>(
              whileStmt->getBody());
        };
      };
    default:
      break;
  }

  clang::Scope* parentBlockBody = scope;
  if (foundBlock) {
    scope = new clang::Scope(scope, 0, getDiagnosticEngine());
    pushCompoundScope();
    addLocalVariablesInSema(foundBlock, scope);
  }
  else if (foundDecl) {
    scope = new clang::Scope(scope, 0, getDiagnosticEngine());
    pushCompoundScope();
    addLocalVariablesInSema(foundDecl, scope);
  };

  comment.parseStatementAnnotation(*container, clangContext, _context, _sema,
      scope, _clangUtils, _rttiTable);

  if (foundBlock) {
    _sema->PopCompoundScope();
    delete scope;
    scope = parentBlockBody;
  }
  else if (foundDecl) {
    _sema->PopCompoundScope();
    delete scope;
    scope = parentBlockBody;
  };
  if (scope != originalScope) {
    _sema->PopCompoundScope();
    delete scope;
    // scope = originalScope;
  };
}

void FramacVisitor::parseFunctionContractComment(
  AnnotationComment& comment, option& /* function_contract */ contract,
  const clang::FunctionDecl* decl) {
  const clang::SourceLocation& clang_loc = comment.getSourceLocation();
  location loc = makeLocation(clang_loc);
  loc->charnum1 += 3;
  if (comment.isLineComment())
   loc->charnum2 -= 1;
  else
    loc->charnum2 -= 3;
  if (contract->is_some) {
    /* behavior */ list oldBehaviors =
      ((function_contract) contract->content.container)->behavior;
    location firstLoc = NULL;
    if (oldBehaviors) {
      behavior oldBehavior = (behavior) oldBehaviors->element.container;
      if (oldBehavior->requires)
        firstLoc = ((predicate_named) oldBehavior->requires->element.container)
          ->pred_loc;
      else if (oldBehavior->assumes)
        firstLoc = ((predicate_named) oldBehavior->assumes->element.container)
          ->pred_loc;
      else if (oldBehavior->post_cond)
        firstLoc = ((post_condition) oldBehavior->post_cond->element.container)
          ->pred->pred_loc;
      else if (oldBehavior->assignements->tag_assigns == WRITES
          && oldBehavior->assignements->cons_assigns.Writes.frm)
        firstLoc = ((from) oldBehavior->assignements->cons_assigns.Writes.frm
            ->element.container)->floc->loc;
      else if (oldBehavior->alloc->tag_allocation == FREEALLOC
          && (oldBehavior->alloc->cons_allocation.FreeAlloc.fst))
        firstLoc = ((term) oldBehavior->alloc->cons_allocation.FreeAlloc.fst
            ->element.container)->loc;
      else if (oldBehavior->alloc->tag_allocation == FREEALLOC
          && (oldBehavior->alloc->cons_allocation.FreeAlloc.snd))
        firstLoc = ((term) oldBehavior->alloc->cons_allocation.FreeAlloc.snd
            ->element.container)->loc;
      else if (oldBehavior->extended && ((behavior_extensions)
            oldBehavior->extended->element.container)->predicates)
        firstLoc = ((predicate_named) ((behavior_extensions)
          oldBehavior->extended->element.container)->predicates->element
            .container)->pred_loc;
    };
    if (firstLoc)
      std::cerr 
        << "Function " << decl->getNameInfo().getAsString()
        << " has two specifications. First one starts at file "
        << firstLoc->filename1
        << ", line "
        << firstLoc->linenum1
        << ". Second one starts at file " << loc -> filename1
        << ", line " << loc -> linenum1 << "." <<std::endl;
     else
      std::cerr 
        << "Function " << decl->getNameInfo().getAsString()
        << " has two specifications. The last one starts at file "
        << loc -> filename1
        << ", line " << loc -> linenum1 << "." <<std::endl;
     exit(2);
  }
  comment.parseFunctionContract(contract, decl, _context, _sema,
      _parents.getScope(), _clangUtils, _rttiTable);
}

void FramacVisitor::parseDefaultComment(AnnotationComment& comment) {
  clang::FileID beginFileId, endFileId;
  unsigned beginOffset, endOffset;
  std::tie(beginFileId, beginOffset) = _context->getSourceManager()
      .getDecomposedLoc(comment.getSourceRange().getBegin());
  std::tie(endFileId, endOffset) = _context->getSourceManager()
      .getDecomposedLoc(comment.getSourceRange().getEnd());
  std::ostringstream msg;
  if (const clang::FileEntry *F = _context->getSourceManager()
      .getFileEntryForID(beginFileId))
    msg << "Unknown kind of comment at " << F->getName().str() << ":"
      << _context->getSourceManager().getLineNumber(beginFileId,beginOffset)
      << ":"
      << _context->getSourceManager().getLineNumber(beginFileId,
          beginOffset) << ":"
      << _context->getSourceManager().getColumnNumber(beginFileId,
          beginOffset)
	    << _context->getSourceManager().getColumnNumber(endFileId,
		      endOffset); // Comments that begin in one file and end in another are already filtered out
  else
    msg << "Unknown kind of comment encountered";
  std::cerr <<  msg.str() << std::endl;
  exit(2);
}

void FramacVisitor::registerTemplateDecl(clang::Decl* Decl) {
  // const clang::CXXRecordDecl *RD
  //   = static_cast<const clang::CXXRecordDecl*>(Decl->getDeclContext());
  // if (RD && RD->getDescribedClassTemplate()
  //       && RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)

  while ((_commentIndex < (int) _annotationCommentList.size()-1)
      && _context->getSourceManager().isBeforeInTranslationUnit(
          _annotationCommentList[_commentIndex+1]->getSourceRange().getEnd(),
          Decl->getSourceRange().getBegin())) {
    AnnotationComment& comment = *_annotationCommentList[++_commentIndex];
    TemplatedAttachedComments::iterator found
      = _templatedAttachedComments.lower_bound(Decl);
    if (found == _templatedAttachedComments.end() || found->first != Decl)
      found = _templatedAttachedComments.insert(found,
          std::make_pair(Decl, std::list<AnnotationComment*>()));
    found->second.push_back(&comment);
  };
  // to uncomment if needed (see VisitTypedef)
  // _tableForWaitingDeclarations.addDeclaration(Decl, _globals);
  // _instanceContexts.removeUnvisited(Decl);
}

void FramacVisitor::registerAttachedNextTemplateDecl(clang::Decl* Decl) {
  // attach annotation comment to decl
  while ((_commentIndex < (int) _annotationCommentList.size()-1)
      && _context->getSourceManager().isBeforeInTranslationUnit(
          _annotationCommentList[_commentIndex+1]->getSourceRange().getEnd(),
          Decl->getSourceRange().getBegin())) {
    AnnotationComment& comment = *_annotationCommentList[++_commentIndex];
    if (comment.getKind() == AnnotationComment::KNext) {
      TemplatedAttachedComments::iterator
          found = _templatedAttachedComments.lower_bound(Decl);
      if (found == _templatedAttachedComments.end() || found->first != Decl)
        found = _templatedAttachedComments.insert(found,
            std::make_pair(Decl, std::list<AnnotationComment*>()));
      found->second.push_back(&comment);
    };
  };
}

void FramacVisitor::readFunctionComments(
  clang::FunctionDecl* Decl, int& nextPreviousComment, bool& isNewTemplate,
    std::list<AnnotationComment*>*& templatedNextAnnotations) {
  std::list<AnnotationComment*>* templatedComments = NULL;
  int previousComment = _commentIndex,
      previousTemplateComment = _templateCommentIndex;
  isNewTemplate = false;
  if (isTemplateInstance(Decl->getTemplateSpecializationKind())) {
    clang::Decl* primaryTemplate = Decl->getPrimaryTemplate();
    isNewTemplate = primaryTemplate;
    if (!isNewTemplate) {
      clang::MemberSpecializationInfo* memberInfo
        = Decl->getMemberSpecializationInfo();
      if (memberInfo)
        primaryTemplate = memberInfo->getInstantiatedFrom();
    };
    assert(primaryTemplate);
    { TemplatedAttachedComments::iterator found
          = _templatedAttachedComments.find(primaryTemplate);
      if (found != _templatedAttachedComments.end())
        templatedComments = &found->second;
    };
    // if (_templateCommentIndex >= -1)
    //   // for the moment, we don't know if we need a stack of instantiations
    //   _templateCommentIndex = -2;
    previousTemplateComment = _templateCommentIndex = findCommentAfterRange(
        primaryTemplate->getSourceRange());
  }
  else if (!Decl->isImplicit())
    advanceCommentUntil(Decl->getSourceRange().getBegin());

  templatedNextAnnotations = NULL;
  if (templatedComments) {
    std::list<AnnotationComment*>::iterator iterEnd = templatedComments->end();
    for (std::list<AnnotationComment*>::iterator iter
        = templatedComments->begin(); iter != iterEnd; ++iter) {
      switch ((*iter)->getKind()) {
        case AnnotationComment::KGlobal:
          // parseTemplatedGlobalComment(**iter, Decl->getDeclContext());
          //   find the template arguments in the instance stack
          //   if !primaryTemplate
          parseGlobalComment(**iter, Decl->getDeclContext());
          break;
        case AnnotationComment::KGhost:
          parseGhostGlobal(**iter, Decl->getDeclContext());
          break;
        case AnnotationComment::KNext:
          if (!templatedNextAnnotations)
            templatedNextAnnotations = new std::list<AnnotationComment*>();
          templatedNextAnnotations->push_back(*iter);
          break;
        default:
          parseDefaultComment(**iter);
          break;
      };
    };
  };
  
  while (previousTemplateComment < _templateCommentIndex) {
    ++previousTemplateComment;
    switch (_annotationCommentList[previousTemplateComment]->getKind()) {
      case AnnotationComment::KGlobal:
        parseGlobalComment(*_annotationCommentList[previousTemplateComment],
            Decl->getDeclContext());
        break;
      case AnnotationComment::KGhost:
          parseGhostGlobal(
            *_annotationCommentList[previousTemplateComment],
            Decl->getDeclContext());
          break;
      case AnnotationComment::KNext:
        // [TODO] for contracts.
        break;
      case AnnotationComment::KNextLoop:
      case AnnotationComment::KNextStatement:
        { std::cerr << "unimplemented next attachment" << std::endl;
          exit(2);
          assert(false);
          // Acsl::FunctionContract functionContract(Decl);
          // Acsl::Parser parser(Decl->getDeclContext(), _context, _sema,
          //    _parents.getScope(), functionContract);
          // parser.parse(*_annotationCommentList[previousTemplateComment]
          //    .getContent());
        };
        break;
      default:
        parseDefaultComment(*_annotationCommentList[previousTemplateComment]);
        break;
    };
  };

  nextPreviousComment = previousComment;

  while (previousComment < _commentIndex) {
    ++previousComment;
    switch (_annotationCommentList[previousComment]->getKind()) {
      case AnnotationComment::KGlobal:
        parseGlobalComment(*_annotationCommentList[previousComment],
            Decl->getDeclContext());
        break;
      case AnnotationComment::KGhost:
          parseGhostGlobal(*_annotationCommentList[previousComment],
                           Decl->getDeclContext());
          break;
      case AnnotationComment::KNext:
        break;
      default:
        parseDefaultComment(*_annotationCommentList[previousComment]);
        break;
    };
  };
}

void FramacVisitor::readContractComments(
  clang::FunctionDecl* Decl, option /* function_contract */& contract,
  bool hasPushedBody, bool& hasParseTemplate, int& nextPreviousComment,
  std::list<AnnotationComment*>* templatedNextAnnotations) {
  if (nextPreviousComment < _commentIndex) {
    if (!hasPushedBody)
      _parents.pushFunctionBody(Decl);
    do {
      ++nextPreviousComment;
      if (_annotationCommentList[nextPreviousComment]->getKind()
          == AnnotationComment::KNext) {
        parseFunctionContractComment(
          *_annotationCommentList[nextPreviousComment], contract, Decl);
      };
    } while (nextPreviousComment < _commentIndex);
    if (!hasPushedBody)
      _parents.popFunctionBody(Decl);
  };
  if (!hasParseTemplate && templatedNextAnnotations
        && !templatedNextAnnotations->empty()) {
    if (!hasPushedBody)
      _parents.pushFunctionBody(Decl);
    hasParseTemplate = true;
    std::list<AnnotationComment*>::iterator
      iterEnd = templatedNextAnnotations->end();
    for (std::list<AnnotationComment*>::iterator iter
        = templatedNextAnnotations->begin(); iter != iterEnd; ++iter)
      // the test can be removed in the case of templatedNextAnnotations
      // see discussion on commit 2c019698
      if ((*iter)->getKind() == AnnotationComment::KNext)
        parseFunctionContractComment(**iter, contract, Decl);
    if (!hasPushedBody)
      _parents.popFunctionBody(Decl);
  };
}

void FramacVisitor::readRecordComments(
  clang::RecordDecl* Decl, const clang::CXXRecordDecl *RD,
  const clang::ClassTemplateSpecializationDecl* TSD,
  bool& isDeportedInstantiation) {
  std::list<AnnotationComment*>* templatedComments = NULL;
  int previousComment = _commentIndex, previousTemplateComment
    = _templateCommentIndex, oldTemplateContext = _templateCommentIndex;
  if (RD /* || hasTemplateContext() */) {
    // [TODO] handle partial instantiation
    if (RD->getDescribedClassTemplate()
        && RD->getDescribedClassTemplate()->getTemplatedDecl()) {
      clang::CXXRecordDecl* primaryRecord
          = RD->getDescribedClassTemplate()->getTemplatedDecl();
      assert(primaryRecord);
      isDeportedInstantiation = true;
      { TemplatedAttachedComments::iterator
        found = _templatedAttachedComments.find(primaryRecord);
        if (found != _templatedAttachedComments.end())
          templatedComments = &found->second;
        // if (_templateCommentIndex >= -1)
        // // for the moment, we don't know if we need a stack of instantiations
        //   _templateCommentIndex = -2;
      };
      previousTemplateComment = _templateCommentIndex = findCommentAfterRange(
          primaryRecord->getSourceRange());
    };
  };

  if (RD && TSD && isTemplateInstance(RD->getTemplateSpecializationKind())
      /* RD->getTemplateSpecializationKind()
          >= clang::TSK_ImplicitInstantiation */) {
    // _parents.setVisitInstances();
    // assert(llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(RD));

    clang::CXXRecordDecl* primaryRecord
      = /* static_cast<const clang::ClassTemplateSpecializationDecl*>(RD) */
          TSD->getSpecializedTemplate()->getTemplatedDecl();
    // RD->getDescribedClassTemplate()->getTemplatedDecl();
    assert(primaryRecord);
    isDeportedInstantiation = true;
    { TemplatedAttachedComments::iterator
      found = _templatedAttachedComments.find(primaryRecord);
      if (found != _templatedAttachedComments.end())
        templatedComments = &found->second;
      // if (_templateCommentIndex >= -1)
      //   // for the moment, we don't know if we need a stack of instantiations
      //   _templateCommentIndex = -2;
    };
    previousTemplateComment = _templateCommentIndex = findCommentAfterRange(
        primaryRecord->getSourceRange());
  };
  if (!isDeportedInstantiation)
    advanceCommentUntil(Decl->getSourceRange().getBegin());

  if (templatedComments) {
    assert(RD);
    std::list<AnnotationComment*>::iterator iterEnd = templatedComments->end();
    for (std::list<AnnotationComment*>::iterator iter
        = templatedComments->begin(); iter != iterEnd; ++iter) {
      switch ((*iter)->getKind()) {
        case AnnotationComment::KGlobal:
          // parseTemplatedGlobalComment(**iter, Decl->getDeclContext());
          //   find the template arguments in the instance stack
          //   if !primaryTemplate
          parseGlobalComment(**iter, Decl->getDeclContext());
          break;
        case AnnotationComment::KGhost:
          parseGhostGlobal(**iter, Decl->getDeclContext());
          break;
        case AnnotationComment::KNext:
          if (RD) {
            std::cerr << "unimplemented next attachment" << std::endl;
            exit(2);
            assert(false);
            // Acsl::ClassContract classContract(RD);
            // Acsl::Parser parser(Decl->getDeclContext(), _context, _sema,
            //     _parents.getScope(), functionContract);
            // parser.parse(*_annotationCommentList[previousComment]
            //     .getContent());
            break;
          };
          break;
        default:
          parseDefaultComment(**iter);
          break;
      };
      std::cerr << "unimplemented template comment" << std::endl;
      exit(2);
      assert(false);
      // Acsl::ClassContract classContract(RD);
      // Acsl::Parser parser(Decl->getDeclContext(), _context, _sema,
      //     _parents.getScope(), classContract);
      // parser.parse(iter->getContent());
    };
  };
  
  while (previousTemplateComment < _templateCommentIndex) {
    ++previousTemplateComment;
    switch (_annotationCommentList[previousTemplateComment]->getKind()) {
    case AnnotationComment::KGlobal:
      parseGlobalComment(*_annotationCommentList[previousTemplateComment],
          Decl->getDeclContext());
      break;
    case AnnotationComment::KGhost:
          parseGhostGlobal(*_annotationCommentList[previousTemplateComment],
                           Decl->getDeclContext());
          break;
    case AnnotationComment::KNext:
        if (RD) { 
          std::cerr << "unimplemented next attachment" << std::endl;
          exit(2);
          assert(false);
          // Acsl::ClassContract classContract(RD);
          // Acsl::Parser parser(Decl->getDeclContext(), _context, _sema,
          //     _parents.getScope(), functionContract);
          // parser.parse(*_annotationCommentList[previousTemplateComment]
          //     .getContent());
          break;
        };
        break;
      default:
        parseDefaultComment(*_annotationCommentList[previousTemplateComment]);
        break;
    };
  };

  while (previousComment < _commentIndex) {
    ++previousComment;
    switch (_annotationCommentList[previousComment]->getKind()) {
      case AnnotationComment::KGlobal:
        parseGlobalComment(*_annotationCommentList[previousComment],
            Decl->getDeclContext());
        break;
      case AnnotationComment::KGhost:
          parseGhostGlobal(*_annotationCommentList[previousComment],
                           Decl->getDeclContext());
          break;
      case AnnotationComment::KNext:
        if (RD) {
          std::cerr << "unimplemented next attachment" << std::endl;
          exit(2);
          assert(false);
          // Acsl::ClassContract classContract(RD);
          // Acsl::Parser parser(Decl->getDeclContext(), _context, _sema,
          //     _parents.getScope(), functionContract);
          // parser.parse(*_annotationCommentList[previousComment]
          //     .getContent());
          break;
        };
        break;
      default:
        parseDefaultComment(*_annotationCommentList[previousComment]);
        break;
    };
  };
  if (RD && !RD->isThisDeclarationADefinition() && _templateCommentIndex >= -1
      && oldTemplateContext < -1)
   _templateCommentIndex = -2;
}

void FramacVisitor::readInnerRecordComments(clang::RecordDecl* Decl) {
  int previousTemplateComment = _templateCommentIndex;
  int previousComment = _commentIndex;
  advanceCommentUntil(Decl->getSourceRange().getEnd());
  while (previousTemplateComment < _templateCommentIndex) {
    ++previousTemplateComment;
    switch (_annotationCommentList[previousTemplateComment]->getKind()) {
      case AnnotationComment::KGlobal:
        parseGlobalComment(*_annotationCommentList[previousTemplateComment],
            Decl);
        break;
      case AnnotationComment::KGhost:
          parseGhostGlobal(*_annotationCommentList[previousTemplateComment],
                           Decl->getDeclContext());
          break;
      case AnnotationComment::KNext:
        { const clang::CXXRecordDecl *RD
            = llvm::dyn_cast<clang::CXXRecordDecl>(Decl);
          if (RD) { 
            std::cerr << "unimplemented next attachment" << std::endl;
            exit(2);
            assert(false);
            // Acsl::ClassContract classContract(RD);
            // Acsl::Parser parser(Decl->getDeclContext(), _context, _sema,
            //     _parents.getScope(), functionContract);
            // parser.parse(*_annotationCommentList[previousTemplateComment]
            //     .getContent());
          };
        };
        break;
      default:
        parseDefaultComment(*_annotationCommentList[previousTemplateComment]);
        break;
    };
  };

  while (previousComment < _commentIndex) {
    ++previousComment;
    switch (_annotationCommentList[previousComment]->getKind()) {
      case AnnotationComment::KGlobal:
        parseGlobalComment(*_annotationCommentList[previousComment], Decl);
        break;
      case AnnotationComment::KGhost:
          parseGhostGlobal(*_annotationCommentList[previousComment],
                           Decl->getDeclContext());
          break;
      case AnnotationComment::KNext:
        { const clang::CXXRecordDecl *RD
            = llvm::dyn_cast<clang::CXXRecordDecl>(Decl);
          if (RD) {
            std::cerr << "unimplemented next attachment" << std::endl;
            exit(2);
            assert(false);
            // Acsl::ClassContract classContract(RD);
            // Acsl::Parser parser(Decl->getDeclContext(), _context, _sema,
            //     _parents.getScope(), functionContract);
            // parser.parse(_annotationCommentList[previousComment]
            //     ->getContent());
          };
        };
        break;
      default:
        parseDefaultComment(*_annotationCommentList[previousComment]);
        break;
    };
  };
}

void FramacVisitor::readGlobalCommentUntil(
  clang::SourceLocation loc, clang::DeclContext* context, bool mayHaveTemplate) 
{
  int previousComment = _commentIndex;
  int previousTemplateComment = _templateCommentIndex;
  if (!mayHaveTemplate)
    assert(previousTemplateComment < -1);
  advanceCommentUntil(loc);
  if (mayHaveTemplate) {
    while (previousTemplateComment < _templateCommentIndex) {
      ++previousTemplateComment;
      switch (_annotationCommentList[previousTemplateComment]->getKind()) {
        case AnnotationComment::KGlobal:
          parseGlobalComment(
            *_annotationCommentList[previousTemplateComment], context);
          break;
        case AnnotationComment::KGhost:
          parseGhostGlobal(
            *_annotationCommentList[previousTemplateComment], context);
          break;
        default:
          parseDefaultComment(*_annotationCommentList[previousTemplateComment]);
          break;
      }
    };
  };
  while (previousComment < _commentIndex) {
    ++previousComment;
    switch (_annotationCommentList[previousComment]->getKind()) {
      case AnnotationComment::KGlobal:
        parseGlobalComment(
          *_annotationCommentList[previousComment], context);
        break;
      case AnnotationComment::KGhost:
          parseGhostGlobal(*_annotationCommentList[previousComment], context);
          break;
      default:
        parseDefaultComment(*_annotationCommentList[previousComment]);
        break;
    }
  };
}

void FramacVisitor::readGlobalComment(clang::Decl* Decl, bool mayHaveTemplate) {
  readGlobalCommentUntil(
    _clangUtils->getBeginLoc(*Decl), Decl->getDeclContext(), mayHaveTemplate);
}

/* bodyBare means that the class has virtual base classes; so the constructor
   should be duplicated with no calls to the virtual base class constructors */
void FramacVisitor::insertConstructorPreambleIn(
    const clang::CXXConstructorDecl& constructor,
    list& /*statement*/ bodyref, bool* shouldDelayInit,
    /* statement */ ForwardReferenceList* bodyBare) {
  clang::CXXConstructorDecl::init_const_reverse_iterator endInitIterator 
      = constructor.init_rend();
  /* insertionPvmtUpdatePoint = insertion position in the statement list:
       = &bodyref(->next)^n
     if some virtual methods appear the vmt initialization will be inserted
       between the statement cell containing *insertionPvmtUpdatePoint
       and **insertionPvmtUpdatePoint.
  */
  list* insertionPvmtUpdatePoint = NULL;
  list* insertionPvmtUpdateBarePoint = NULL;
  list* insertionPvmtUpdatePointBeforeBare = NULL;
  list body_head = bodyref;
  list body_bare_head = NULL;

  // According to 12.7, the initialization is done in the following
  // order:
  // Base classes initialization
  // Virtual Method Table initialization
  // Non-static member initialization
  // we build it in reverse, so that we can add statement in front of
  // the existing body.
  for (clang::CXXConstructorDecl::init_const_reverse_iterator initIterator
      = constructor.init_rbegin(); initIterator != endInitIterator;
      ++initIterator) {
    const clang::CXXCtorInitializer* initializer = *initIterator;
    assert(initializer);
    bool isBareField = false;
    bool isBaseVirtual = false;
    if (initializer->isBaseInitializer()) {
      clang::QualType baseType = initializer->getTypeSourceInfo()
        ->getType();
      variable thisVariable = variable_FunctionParameter("this");
      exp_node node = exp_node_Variable(thisVariable);
      location loc1 = makeLocation(constructor.getSourceRange());
      location loc2 = copy_loc(loc1);
      location loc3 = copy_loc(loc1);
      qual_type baseTypePointer =
        makeDefaultNameType(constructor.getLocation(), baseType);
      pkind pointerKind = pkind_PDataPointer(baseTypePointer);
      baseTypePointer = qual_type_cons(NULL, typ_Pointer(pointerKind));
      const clang::CXXRecordDecl* base = baseType.getTypePtr()
          ->getPointeeCXXRecordDecl();
      if (!base)
        base = baseType.getTypePtr()->getCanonicalTypeInternal().getTypePtr()
            ->getAsCXXRecordDecl();
      if (base) {
        if (hasInstanceContext()) {
          _tableForWaitingDeclarations.ensureGeneration(base, unvisitedDecls());
        }
        else if (shouldDelayInit && !*shouldDelayInit)
          *shouldDelayInit = !_tableForWaitingDeclarations.hasVisited(base);
      };

      isBaseVirtual = initializer->isBaseVirtual();
      if (base)
         isBareField = _rttiTable.hasVirtualBaseClasses(base);
      exp_node shiftNode = exp_node_PointerCast(baseTypePointer,
          reference_or_pointer_kind_RPKStaticBasePointer(),
          expression_cons(loc1,node));
      _implicitThisStar = expression_cons(loc3,
          exp_node_Dereference(expression_cons(loc2,shiftNode)));
      _isImplicitThisBare = isBareField;
      if (isBareField)
        insertionPvmtUpdatePointBeforeBare = &body_head;
    }
    else if (initializer->isAnyMemberInitializer()) {
      variable thisVariable = variable_FunctionParameter("this");
      exp_node node = exp_node_Variable(thisVariable);
      location loc1 = makeLocation(constructor.getSourceRange());
      location loc2 = copy_loc(loc1);
      location loc3 = copy_loc(loc1);
      clang::FieldDecl* field = initializer->getAnyMember();
      _memberType = field->getType()->getTypeClass();
      const clang::RecordDecl* base = field->getParent();
      if (base) {
        if (hasInstanceContext()) {
          _tableForWaitingDeclarations.ensureGeneration(base, unvisitedDecls());
        }
        else if (shouldDelayInit && !*shouldDelayInit)
          *shouldDelayInit = !_tableForWaitingDeclarations.hasVisited(base);
      };
      const char* field_name = _clangUtils->get_field_name(field);

      node = exp_node_Dereference(expression_cons(loc1,node));
      
      if (initializer->isIndirectMemberInitializer()) {
        clang::IndirectFieldDecl* indirect_fd =
          initializer->getIndirectMember() ;      
        
        for(auto it=indirect_fd->chain_begin();
            it+1 != indirect_fd->chain_end(); it++) {
          node =
            exp_node_FieldAccess(
              expression_cons(copy_loc(loc1), node),
              strdup(_clangUtils->findAnonymousName(*it).c_str()));
        }
      };
      
      _implicitThisStar=
        expression_cons(
          loc3,
          exp_node_FieldAccess(expression_cons(loc2, node), field_name));
      if(field->getType()->isReferenceType())
        _implicitThisStar =
          expression_cons(
            copy_loc(loc3),
            exp_node_Unary_operator(uokind_UOCastDerefInit(),_implicitThisStar));
    }
    else {
      std::cerr << "Unsupported constructor initializer:"
          << constructor.getDeclName().getAsString ()
          << "\nAborting\n";
      exit(2);
    };
    /* statement */ list temp = NULL;
    exp_node init;
    init = makeExpression(initializer->getInit(), shouldDelayInit, &temp);
    if (init) {
      statement initPart;
      if (!isBaseVirtual)
        initPart = statement_Expression(
            makeLocation(constructor.getSourceRange()),
            expression_cons(makeLocation(initializer->getInit()
                ->getSourceRange()), init));
      else
        initPart = statement_VirtualExpression(
            makeLocation(constructor.getSourceRange()),
            expression_cons(makeLocation(initializer->getInit()
                ->getSourceRange()), init));
      // if we are done with initializer of members, this is the place
      // where to insert initialization of virtual method table
      if (!_cleanups.empty()) {
        ForwardReferenceList header(temp);
        /* statement */ list* cursor = header.getBack()
          ? &header.getBack()->next : &header.getFront();
        header.insertContainer(initPart);
        makeCleanupsStmts(header, cursor, initPart->cons_statement.Expression
          .expr, constructor.getDeclContext(), NULL);
        if (initializer->isBaseInitializer() && !insertionPvmtUpdatePoint)
          insertionPvmtUpdatePoint = &header.getBack()->next;
        ForwardReferenceList tail(body_head);
        if (!isBareField && insertionPvmtUpdatePointBeforeBare == &body_head)
          insertionPvmtUpdatePointBeforeBare = &header.getBack()->next;
        header.append(tail);
        if (bodyBare && !isBaseVirtual) {
          list cursor = temp, endCursor = body_head;
          list tempBare = NULL;
          ForwardReferenceList headerBare(tempBare);
          while (cursor != endCursor) {
            assert(cursor != NULL);
            if (insertionPvmtUpdatePoint && *insertionPvmtUpdatePoint == cursor)
              insertionPvmtUpdateBarePoint = &headerBare.getBack()->next;
            headerBare.insertContainer(statement_dup((statement)
                cursor->element.container));
            cursor = cursor->next;
          };
          if (tempBare) {
            headerBare.getBack()->next = body_bare_head;
            body_bare_head = tempBare;
          };
        };
        body_head = temp;
      }
      else {
        bool doesNeedUpdate = !isBareField
            && insertionPvmtUpdatePointBeforeBare == &body_head;
        body_head = cons_container(initPart, body_head);
        if (doesNeedUpdate)
          insertionPvmtUpdatePointBeforeBare = &body_head->next;
        if (bodyBare && !isBaseVirtual)
          body_bare_head = cons_container(statement_dup(initPart),
            body_bare_head);
        if (initializer->isBaseInitializer() && !insertionPvmtUpdatePoint) {
          insertionPvmtUpdatePoint = &body_head->next;
          if (bodyBare && !isBaseVirtual)
            insertionPvmtUpdateBarePoint = &body_bare_head->next;
        }
        if(temp) {
          list t = temp;
          list tempBare = NULL;
          ForwardReferenceList headerBare(tempBare);
          if (bodyBare && !isBaseVirtual)
            headerBare.insertContainer(statement_dup((statement)
                t->element.container));
          while (t->next) {
            t = t->next;
            if (bodyBare && !isBaseVirtual)
              headerBare.insertContainer(statement_dup((statement)
                  t->element.container));
          };
          t->next = body_head;
          body_head = temp;
          if (bodyBare && !isBaseVirtual) {
            if (tempBare) {
              headerBare.getBack()->next = body_bare_head;
              body_bare_head = tempBare;
            };
          };
        }
      };
    }
    else {
      while (temp) {
        assert(false); // should not be called
        free_statement((statement) temp->element.container);
        list toBeFreed = temp;
        temp = temp->next;
        free(toBeFreed);
      };
    }
  };
  // update the body
  bodyref = body_head;
  if (bodyBare) {
    if (body_bare_head) {
      ForwardReferenceList first(body_bare_head);
      first.append(*bodyBare);
      bodyBare->getFront() = body_bare_head;
      if (!bodyBare->getBack())
        bodyBare->resetBack(first.getBack());
    };
    if (!insertionPvmtUpdateBarePoint)
      insertionPvmtUpdateBarePoint = &bodyBare->getFront();
    location loc = makeLocation(constructor.getSourceRange());
    _rttiTable.addBarePvmtSetter(*_clangUtils,
      const_cast<clang::CXXRecordDecl*>(constructor.getParent()),
      *insertionPvmtUpdateBarePoint, loc);
    free_location(loc);
  };
  // in case of a class with no inheritance, the first step is
  // to set up the virtual method table
  if (insertionPvmtUpdatePointBeforeBare
      && insertionPvmtUpdatePointBeforeBare != &body_head) {
    location loc = makeLocation(constructor.getSourceRange());
    _rttiTable.addPvmtSetterForBare(
      *_clangUtils,
      const_cast<clang::CXXRecordDecl*>(constructor.getParent()),
      *insertionPvmtUpdatePointBeforeBare,loc);
    free_location(loc);
  };

  if (!insertionPvmtUpdatePoint)
    insertionPvmtUpdatePoint = (list*) &bodyref;
  if (constructor.getParent() == _rttiTable.getCurrentClass())
    _rttiTable.addPvmtSetter(*insertionPvmtUpdatePoint);
  else if (_rttiTable.hasVirtualMethods(constructor.getParent())) {
    location loc = makeLocation(constructor.getSourceRange());
    // llvm::outs() << "constructor for class ";
    // constructor.getParent()->getNameForDiagnostic(llvm::outs(),
    //     _sema->getPrintingPolicy(),true);
    // llvm::outs() << " while current class is ";
    // _rttiTable.getCurrentClass()->getNameForDiagnostic(llvm::outs(),
    //     _sema->getPrintingPolicy(),true);
    // llvm::outs() << "\n";
    _rttiTable.addPvmtSetter(
      *_clangUtils,
      const_cast<clang::CXXRecordDecl*>(constructor.getParent()),
      *insertionPvmtUpdatePoint,loc);
    free_location(loc);
  };
}

/* bodyBare means that the class has virtual base classes; so the destructor 
   should be duplicated with no calls to the virtual base class destructors */
void FramacVisitor::insertDestructorPreambleIn(
    const clang::CXXDestructorDecl& destructor,
    option /* statement list */ bodyref,
    /* statement */ ForwardReferenceList* bodyBare) {
  const clang::CXXRecordDecl* parent = destructor.getParent();
  if (!parent)
    return;

  list* insertionPvmtUpdatePoint = (list*) &bodyref->content.container;
  list* insertionPvmtUpdateBarePoint = bodyBare ? &bodyBare->getFront() : NULL;
  list* insertionPvmtUpdatePointBeforeBare = NULL;
  std::vector<const clang::CXXRecordDecl*> virtualBases;
  if (parent == _rttiTable.getCurrentClass()) {
    _rttiTable.addPvmtSetter(*insertionPvmtUpdatePoint);
    virtualBases = _rttiTable.getCurrentClassInfo()->getVirtualBases();
    if (bodyBare && !virtualBases.empty()) {
      location loc = makeLocation(destructor.getSourceRange());
      _rttiTable.addBarePvmtSetter(*_clangUtils,
        const_cast<clang::CXXRecordDecl*>(parent),
        *insertionPvmtUpdateBarePoint,
        loc);
      free_location(loc);
    };
  }
  else if (_rttiTable.hasVirtualMethods(parent)) {
    location loc = makeLocation(destructor.getSourceRange());
    _rttiTable.addPvmtSetter(*_clangUtils,
      const_cast<clang::CXXRecordDecl*>(parent),
      *insertionPvmtUpdatePoint, loc);
    virtualBases = _rttiTable.getClassInfo(parent)->getVirtualBases();
    if (bodyBare && !virtualBases.empty())
      _rttiTable.addBarePvmtSetter(*_clangUtils,
        const_cast<clang::CXXRecordDecl*>(parent),
        *insertionPvmtUpdateBarePoint,
        loc);
    free_location(loc);
  };

  ForwardReferenceList body(*(list*) &bodyref->content.container);
  list body_head = NULL;
  clang::CXXRecordDecl::base_class_const_iterator endBase = parent->bases_end(),
      iterBase = parent->bases_begin();
  for (; iterBase != endBase; ++iterBase) {
    const clang::Type* baseType = iterBase->getType().getTypePtr();
    const clang::CXXRecordDecl* base = baseType->getAsCXXRecordDecl();
    if (!base)
      base = baseType->getCanonicalTypeInternal().getTypePtr()
          ->getAsCXXRecordDecl();
    if (!base || base->hasTrivialDestructor())
      continue;
    // if (hasInstanceContext()) {
    //   _tableForWaitingDeclarations.ensureGeneration(base,
    //       const_cast<Visitor*>(this)->unvisitedDecls());
    // }
    // else if (shouldDelayInit && !*shouldDelayInit)
    //   *shouldDelayInit = !_tableForWaitingDeclarations.hasVisited(base);

    variable thisVariable = variable_FunctionParameter("this");
    exp_node node = exp_node_Variable(thisVariable);
    location loc = makeLocation(destructor.getSourceRange());
    qual_type baseTypePointer = makeDefaultNameType(
      _clangUtils->getBeginLoc(*iterBase),iterBase->getType());
    pkind pointerKind = pkind_PDataPointer(baseTypePointer);
    baseTypePointer = qual_type_cons(NULL, typ_Pointer(pointerKind));

    bool isBaseVirtual = iterBase->isVirtual();
    exp_node shiftNode = NULL;
    bool isBareField = _rttiTable.hasVirtualBaseClasses(base);
    shiftNode = exp_node_PointerCast(baseTypePointer,
        reference_or_pointer_kind_RPKStaticBasePointer(),
        expression_cons(loc,node));
    if (isBaseVirtual) {
      std::vector<const clang::CXXRecordDecl*>::iterator
        iterEnd = virtualBases.end(), iter;
      for (iter = virtualBases.begin(); iter != iterEnd; ++iter)
        if (*iter == base) break;
      assert(iter != iterEnd);
      virtualBases.erase(iter);
    };

    qualified_name name
      = _clangUtils->makeQualifiedName(*base->getDestructor());
    if (isBareField)
      _rttiTable.addBareToQualification(name);
    list /* expression */ arguments
      = cons_container(expression_cons(copy_loc(loc),shiftNode), NULL);
    signature sig = _clangUtils->makeSignature(*base->getDestructor());
    expression call = expression_cons(copy_loc(loc),
      exp_node_Static_call(name, sig, funkind_FKDestructor(true),
        arguments, tkind_TStandard(), false));
    if (isBareField) {
      if (!body_head)
        insertionPvmtUpdatePointBeforeBare = &body_head;
      else {
        ForwardReferenceList tail(body_head);
        insertionPvmtUpdatePointBeforeBare = &tail.getBack()->next;
      };
    };

    statement initPart;
    if (!isBaseVirtual)
      initPart = statement_Expression(copy_loc(loc), call);
    else
      initPart = statement_VirtualExpression(copy_loc(loc), call);
    bool doesNeedUpdate = insertionPvmtUpdatePointBeforeBare == &body_head;
    body_head = cons_container(initPart, body_head);
    if (doesNeedUpdate)
      insertionPvmtUpdatePointBeforeBare = &body_head->next;
  };
  if (bodyBare) {
    list cursor = body_head;
    while (cursor) {
      bodyBare->insertContainer(statement_dup((statement)
          cursor->element.container));
      cursor = cursor->next;
    };
  }

  std::vector<const clang::CXXRecordDecl*>::const_reverse_iterator
    vendBase = virtualBases.rend(), viterBase = virtualBases.rbegin();
  for (; viterBase != vendBase; ++viterBase) {
    const clang::CXXRecordDecl* base = *viterBase;
    if (base->hasTrivialDestructor())
      continue;
    // if (hasInstanceContext()) {
    //   _tableForWaitingDeclarations.ensureGeneration(base,
    //       const_cast<Visitor*>(this)->unvisitedDecls());
    // }
    // else if (shouldDelayInit && !*shouldDelayInit)
    //   *shouldDelayInit = !_tableForWaitingDeclarations.hasVisited(base);

    variable thisVariable = variable_FunctionParameter("this");
    exp_node node = exp_node_Variable(thisVariable);
    location loc = makeLocation(destructor.getSourceRange());
    tkind base_kind = _clangUtils->makeTemplateKind(base);
    qual_type baseType = qual_type_cons(NULL,
      typ_Pointer(pkind_PDataPointer(qual_type_cons(NULL,
        typ_Struct(_clangUtils->makeQualifiedName(*base), base_kind)))));
    exp_node shiftNode = exp_node_PointerCast(baseType,
        reference_or_pointer_kind_RPKStaticBasePointer(),
        expression_cons(loc, node));

    qualified_name name
      = _clangUtils->makeQualifiedName(*base->getDestructor());
    if (_rttiTable.hasVirtualBaseClasses(base))
      _rttiTable.addBareToQualification(name);
    list /* expression */ arguments
      = cons_container(expression_cons(copy_loc(loc),shiftNode), NULL);
    signature sig = _clangUtils->makeSignature(*base->getDestructor());
    expression call = expression_cons(copy_loc(loc),
      exp_node_Static_call(name, sig, funkind_FKDestructor(true),
        arguments, tkind_TStandard(), false));
    body.insertContainer(statement_VirtualExpression(copy_loc(loc), call));
  };

  if (insertionPvmtUpdatePointBeforeBare) {
    location loc = makeLocation(destructor.getSourceRange());
    _rttiTable.addPvmtSetterForBare(*_clangUtils, parent,
      *insertionPvmtUpdatePointBeforeBare,loc);
    free_location(loc);
  };
  if (body_head) {
    if (body.getBack())
      body.getBack()->next = body_head;
    else
      bodyref->content.container = body_head;
  };
}

void FramacVisitor::addDelayedImplementation(
    translation_unit_decl delayedFunc, clang::FunctionDecl* Decl,
    const char* name, option /*statement list */& delayedBody,
    /* statement list */ option bodyBare /* may be NULL */) {
  if (delayedFunc->cons_translation_unit_decl.Function.fun_spec->is_some) {
    free_function_contract((function_contract) delayedFunc
      ->cons_translation_unit_decl.Function.fun_spec->content.container);
    free(delayedFunc->cons_translation_unit_decl.Function.fun_spec);
    delayedFunc->cons_translation_unit_decl.Function.fun_spec = opt_none();
  };
  free(delayedFunc->cons_translation_unit_decl.Function.body);
  delayedFunc->cons_translation_unit_decl.Function.body = delayedBody;
  delayedBody = NULL;
  if (delayedFunc->cons_translation_unit_decl.Function.fun_name
      ->tag_decl_or_impl_name == DECLARATION) {
    free_decl_or_impl_name(delayedFunc->cons_translation_unit_decl
          .Function.fun_name);
    qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
    free(const_cast<char*>(qual->decl_name));
    qual->decl_name = strdup(name);
    delayedFunc->cons_translation_unit_decl.Function.fun_name
      = decl_or_impl_name_Implementation(qual);
  };
  _delayedImplementations.insertContainer(delayedFunc);
  if (bodyBare) {
    qualified_name bareName = qualified_name_dup(delayedFunc
      ->cons_translation_unit_decl.Function.fun_name->cons_decl_or_impl_name
      .Implementation.name);
    _rttiTable.addBareToQualification(bareName);
    /* arg_decl */ list bareArgs = NULL;
    if (delayedFunc->cons_translation_unit_decl.Function.args) {
      list temp = delayedFunc->cons_translation_unit_decl.Function.args;
      ForwardReferenceList headerArgs(bareArgs);
      headerArgs.insertContainer(arg_decl_dup((arg_decl)
        temp->element.container));
      temp = temp->next;
      while (temp) {
        headerArgs.insertContainer(
          arg_decl_dup((arg_decl) temp->element.container));
        temp = temp->next;
      };
    }
    translation_unit_decl bareDeclFun = translation_unit_decl_Function(
      decl_or_impl_name_Implementation(bareName),
      funkind_dup(delayedFunc->cons_translation_unit_decl.Function.kind),
      copy_loc(delayedFunc->cons_translation_unit_decl.Function.fun_loc),
      qual_type_dup(delayedFunc->cons_translation_unit_decl.Function
        .return_type),
      bareArgs,
      bodyBare,
      delayedFunc->cons_translation_unit_decl.Function.is_extern_c,
      delayedFunc->cons_translation_unit_decl.Function.is_ghost,
      delayedFunc->cons_translation_unit_decl.Function.is_variadic,
      tkind_dup(delayedFunc->cons_translation_unit_decl.Function
          .template_kind),
      delayedFunc->cons_translation_unit_decl.Function.has_further_definition,
      opt_none() /* throws */,
      opt_none() /* spec */);
    _delayedImplementations.insertContainer(bareDeclFun);
  }
}

bool FramacVisitor::VisitFunctionDecl(clang::FunctionDecl* Decl) {
  if (!_ghost && isGhostDecl(Decl)) return true;

  // do not translate friend declaration: they're only there for
  // typechecking C++ and won't be used afterwards
  if (llvm::dyn_cast<clang::FriendDecl>(Decl)) return true;

  // Deleted functions are only useful in overload resolution.
  // We do not need them in the translation itself.
  if (Decl->isDeleted()) return true;

  if (/* _parents. */ hasTemplateContext() && _parents.isSemanticLocalClass())
    handleSemanticPostVisit(Decl->getDeclContext());
  else
    handlePostVisit(Decl->getLexicalDeclContext(), Decl->getDeclContext());
  if (hasTemplateContext())
  { registerTemplateDecl(Decl);
    return true;
  };
  if (Decl->getTemplatedKind() == clang::FunctionDecl::TK_FunctionTemplate) {
    registerAttachedNextTemplateDecl(Decl);
    return true;
  };


  int builtinID = Decl->getBuiltinID();
  if (builtinID > 0 && 
      !_context->BuiltinInfo.isPredefinedLibFunction(builtinID)) {
    // clang internal builtin or architecture specific function. Don't try
    // to visit it further.
    ensureBuiltinDeclaration(builtinID, Decl);
    _tableForWaitingDeclarations.addDeclaration(Decl, _globals);
    _instanceContexts.removeUnvisited(Decl);
    return true;
  };
  // Name
  // TODO: decompose the qualified name
  // Cf NestedNameSpecifier
  tkind templateExtension = NULL;
  const char* name = copy_string(Decl->getNameAsString ());
  if (Decl->getTemplateSpecializationKind() >= clang::TSK_ImplicitInstantiation)
  { clang::FunctionTemplateSpecializationInfo* info
      = Decl->getTemplateSpecializationInfo();
    if (info) {
      templateExtension =
        tkind_TTemplateInstance(_clangUtils->getTemplateExtension(info));
    };
  }
  if (!templateExtension)
    templateExtension = tkind_TStandard();

  int nextPreviousComment = _commentIndex;
  std::list<AnnotationComment*>* templatedNextAnnotations = NULL;
  bool isNewTemplate = false;
  readFunctionComments(Decl, nextPreviousComment, isNewTemplate,
      templatedNextAnnotations);

  bool isInstance = isTemplateInstance(
      Decl->getTemplateSpecializationKind());
  // Location
  location loc = makeLocation(Decl->getSourceRange());
  // Return type
  qual_type return_type =
    makeDefaultNameType(Decl->getLocation(), Decl->getReturnType());
  // Parameters
  list /*arg_decl*/ prms = NULL;
  pushInstanceFunction(); // arguments may depend from non-generated classes
  for (int i = Decl->getNumParams() - 1;i>=0;i--) {
    arg_decl cdecl = (arg_decl)malloc(sizeof(*cdecl));
    prms = cons_container(cdecl,prms);
    const clang::ParmVarDecl *prm = Decl->getParamDecl(i);
    if (prm->getNameAsString().size() > 0)
      cdecl->arg_name = copy_string(prm->getNameAsString());
    else {
      std::ostringstream out;
      out << "__frama_c_arg_" << i;
      cdecl->arg_name = copy_string(out.str());
    };
    cdecl->arg_type =
      makeDefaultNameType(prm->getLocation(), prm->getOriginalType());
    cdecl->arg_loc = makeLocation(prm->getSourceRange());
  }

  // Body
  option /*statement list */ body = opt_none();
  option /*statement list */ delayedBody = NULL;
  option /* function_contract */ contract = opt_none();
  clang::Decl::Kind contextKind = Decl->getDeclContext()->getDeclKind();
  bool hasParseTemplate = false;
  bool isImplicitFunction = false;
  if (Decl->doesThisDeclarationHaveABody()) {
    _parents.pushFunctionBody(Decl);
    _typeFunctionResult = return_type;
    readContractComments(Decl, contract, true /* hasPushedBody */,
        hasParseTemplate, nextPreviousComment, templatedNextAnnotations);
    if (contract->is_some)
      _tableForWaitingDeclarations.visitFunctionDefinitionWithContract(Decl);
    // if (isInstance) {
      // sometimes template are before their use and the instantiation
      //   point needs some further declarations (isInstance).
      // sometimes template are after their use and the function use
      //   forward instance declarations (no way to characterize this fact).
      // pushInstanceFunction();
      if (isInstance && Decl->getPrimaryTemplate())
        _clangUtils->pushTemplateInstance(Decl->getPrimaryTemplate(),
            Decl->getTemplateSpecializationArgs());
    // };
    if (clang::CXXMethodDecl::classof(Decl)) {
      clang::CXXMethodDecl* meth = static_cast<clang::CXXMethodDecl*>(Decl);
      /* default assign operator is not defined correctly
        (returns *this instead of this) and others default
        methods seem to be undefined anyway. Just focus on the
        user-provided ones.
      */
      if (_clangUtils->doesGenerateImplicitMethods() || meth->isUserProvided())
      { bool shouldDelay = false;
        list /*<statement>*/ content = makeCodeBlock(Decl->getBody(),
            Decl->getDeclContext(), Decl,
            (contextKind == clang::Decl::TranslationUnit
              || contextKind == clang::Decl::LinkageSpec
              || contextKind == clang::Decl::Namespace) ? NULL : &shouldDelay);
        if (!shouldDelay) {
          free(body);
          body = opt_some_container(content);
        }
        else
          delayedBody = opt_some_container(content);
      }
      else {
        isImplicitFunction = true;
        std::vector<const clang::Decl*> waitDeclarations;
        popInstanceFunction(waitDeclarations);
        if (isInstance && Decl->getPrimaryTemplate())
          _clangUtils->popTemplateInstance(Decl->getPrimaryTemplate());
      }
    }
    else {
      bool shouldDelay = false;
      list /*<statement>*/ content = makeCodeBlock(Decl->getBody(),
          Decl->getDeclContext(), Decl,
          (contextKind == clang::Decl::TranslationUnit
            || contextKind == clang::Decl::LinkageSpec
            || contextKind == clang::Decl::Namespace) ? NULL : &shouldDelay);
      if (!shouldDelay) {
        free(body);
        body = opt_some_container(content);
      }
      else
        delayedBody = opt_some_container(content);
    };
    _typeFunctionResult = NULL;
    _parents.popFunctionBody(Decl);
  } else { // declaration only
    // just forget missing generation dependencies for arguments
    // when the body is missing
    std::vector<const clang::Decl*> waitDeclarations;
    popInstanceFunction(waitDeclarations);

    readContractComments(
      Decl, contract, false /* hasPushedBody */,
      hasParseTemplate, nextPreviousComment, templatedNextAnnotations);
    if (contract->is_some)
      _tableForWaitingDeclarations.visitFunctionDefinitionWithContract(Decl);
    if (templatedNextAnnotations)
      delete templatedNextAnnotations;
  }

  bool isGenerationEffective = true;
  if (contextKind == clang::Decl::TranslationUnit
      || contextKind == clang::Decl::LinkageSpec
      //|| contextKind == clang::Decl::Namespace
      /* !_parents.hasLexicalContext() */) {
    assert(!delayedBody);
    decl_or_impl_name decl_name = NULL;
    if (Decl->getDeclContext() == Decl->getLexicalDeclContext())
      decl_name = decl_or_impl_name_Declaration(name);
    else {
      qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
      free(const_cast<char*>(qual->decl_name));
      qual->decl_name = name;
      decl_name = decl_or_impl_name_Implementation(qual);
    };
    translation_unit_decl func =
      translation_unit_decl_Function(
        decl_name, funkind_FKFunction(), loc, return_type, prms, body,
        Decl->isInExternCContext() /* || Decl->isExternCContext() */, _ghost,
        Decl->isVariadic(), templateExtension,
        false /* has_further_definition */, opt_none() /* throws */, contract);
    if (!contract->is_some) {
      _tableForWaitingDeclarations.addUpdateFunction(
        Decl,
        &func->cons_translation_unit_decl.Function.has_further_definition);
    };
    if (body->is_some /* && isInstance */) {
      std::vector<const clang::Decl*> waitDeclarations;
      popInstanceFunction(waitDeclarations);
      if (isInstance && Decl->getPrimaryTemplate())
        _clangUtils->popTemplateInstance(Decl->getPrimaryTemplate());
      if (!waitDeclarations.empty()) {
        isGenerationEffective = false;
        _tableForWaitingDeclarations.addIncompleteFunction(Decl,
            waitDeclarations, func);
      }
      else {
        _globals.insertContainer(func);
      };
    }
    else {
      _globals.insertContainer(func);
    }
  }
  else {
    if (Decl->getDeclContext()->isRecord() /* _parents.isClass() */) {
      const clang::CXXRecordDecl* current_class =
        llvm::cast<const clang::CXXRecordDecl>(Decl->getDeclContext());
      /* need to resynchronize RTTI table if the definition is outside of
         the class body. */
      option /* statement list */ bodyref = delayedBody ? delayedBody : body;
      option bodyBare = NULL;
      funkind kind;
      if (Decl->getCanonicalDecl()->getStorageClass() == clang::SC_Static ||
          Decl->getNameAsString() == "operator new"    ||
          Decl->getNameAsString() == "operator new[]"  ||
          Decl->getNameAsString() == "operator delete" ||
          Decl->getNameAsString() == "operator delete[]")
        kind = funkind_FKFunction();
      else {
        auto meth = llvm::cast<const clang::CXXMethodDecl>(Decl);
        if (meth->isVirtual()
            && Decl->getDeclContext() == Decl->getLexicalDeclContext())
          _rttiTable.addVirtualMethod(meth);
        if (llvm::isa<clang::CXXConstructorDecl>(Decl)) {
          kind = funkind_FKConstructor(true);
          if (strlen(name) == 0) {
            free(const_cast<char*>(name));
            name = strdup("constructor-special");
          };
          bool hasVirtualBaseClasses =
            _rttiTable.hasVirtualBaseClasses(current_class);
          if (bodyref->is_some) {
            bool shouldDelay = false;
            /* statement */ list bareResult = NULL;
            ForwardReferenceList headerBare(bareResult);
            if (hasVirtualBaseClasses &&
                _clangUtils->doesGenerateBareFunctions() &&
                (list) bodyref->content.container) {
              list cursor = (list) bodyref->content.container;
              headerBare.insertContainer((statement) cursor->element.container);
              cursor = cursor->next;
              while (cursor) {
                headerBare.insertContainer(
                  (statement) cursor->element.container);
                cursor = cursor->next;
              }
            }
            insertConstructorPreambleIn(
              *llvm::cast<const clang::CXXConstructorDecl>(Decl),
              *(list*)&bodyref->content.container, &shouldDelay,
              (hasVirtualBaseClasses&& _clangUtils->doesGenerateBareFunctions())
              ? &headerBare : NULL);
            if ((shouldDelay || (hasVirtualBaseClasses
                                 && _clangUtils->doesGenerateBareFunctions()))
                && !delayedBody) {
              delayedBody = body;
              body = opt_none();
            };
            if (bareResult)
              bodyBare = opt_some_container(bareResult);
          }
          else if (hasVirtualBaseClasses
                   && _clangUtils->doesGenerateBareFunctions())
            bodyBare = opt_none();
        } else if (llvm::isa<clang::CXXDestructorDecl>(Decl)) {
          // the same as for FKCONSTRUCTOR
          kind = funkind_FKDestructor(true);
          if (bodyref->is_some) {
            /* statement */ list bareResult = NULL;
            bool hasVirtualBaseClasses =
              _rttiTable.hasVirtualBaseClasses(current_class);
            ForwardReferenceList headerBare(bareResult);
            if (hasVirtualBaseClasses && (list) bodyref->content.container) {
              list cursor = (list) bodyref->content.container;
              headerBare.insertContainer((statement) cursor->element.container);
              cursor = cursor->next;
              while (cursor) {
                headerBare.insertContainer(
                  (statement) cursor->element.container);
                cursor = cursor->next;
              };
            };
            insertDestructorPreambleIn(
              *llvm::cast<const clang::CXXDestructorDecl>(Decl),
              bodyref,
              (hasVirtualBaseClasses &&
               _clangUtils->doesGenerateBareFunctions())
              ? &headerBare : NULL);
            if (hasVirtualBaseClasses &&
                _clangUtils->doesGenerateBareFunctions())
              { bodyBare = opt_some_container(bareResult);
                if (!delayedBody) {
                  delayedBody = body;
                  body = opt_none();
                };
              };
          }
          else if (_clangUtils->doesGenerateBareFunctions()
                   && _rttiTable.hasVirtualBaseClasses(current_class))
            bodyBare = opt_none();
        } else {
          kind = _clangUtils->cv_meth(meth);
        };
        arg_decl cdecl = (arg_decl)malloc(sizeof(*cdecl));
        prms = cons_container(cdecl,prms);
        cdecl->arg_name = copy_string("this");
        clang::QualType typeClass(current_class->getTypeForDecl(), 0);
        qual_type this_type =
          _clangUtils->makeType(Decl->getLocation(), typeClass);
        this_type->qualifier =
          cv_this_ptr(static_cast<clang::CXXMethodDecl*>(Decl));
        pkind pointerKind = pkind_PDataPointer(this_type);
        cdecl->arg_type = qual_type_cons(NULL, typ_Pointer(pointerKind));
        cdecl->arg_loc = makeLocation(Decl->getSourceRange());
      }
      bool is_implicit = isImplicitFunction || Decl->isDefaulted();
      bool is_variadic = Decl->isVariadic();
      if (_parents.isClass()) {
        if (body->is_some /* && isInstance */) {
          std::vector<const clang::Decl*> waitDeclarations;
          popInstanceFunction(waitDeclarations);
          if (isInstance && Decl->getPrimaryTemplate())
            _clangUtils->popTemplateInstance(Decl->getPrimaryTemplate());
          if (!waitDeclarations.empty()) {
            if (Decl->getDeclContext()->isRecord()) {
              assert(llvm::dyn_cast<clang::RecordDecl>(Decl->getDeclContext()));
              const clang::Decl* decl = static_cast<const clang::RecordDecl*>
                  (Decl->getDeclContext());
              for (int index = waitDeclarations.size()-1; index >= 0; --index) {
                const clang::Decl* waitingDecl = waitDeclarations[index];
                if (waitingDecl == decl || waitingDecl == Decl)
                  waitDeclarations.erase(waitDeclarations.begin() + index);
                else {
                  bool hasFound = false;
                  for (int i = 0; !hasFound && i < index; ++i)
                    hasFound = (waitingDecl == waitDeclarations[i]);
                  if (hasFound)
                    waitDeclarations.erase(waitDeclarations.begin() + index);
                };
              };
            };
          };
          if (!waitDeclarations.empty()) {
            qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
            free(const_cast<char*>(qual->decl_name));
            qual->decl_name = name;
            translation_unit_decl func =
              translation_unit_decl_Function(
                decl_or_impl_name_Implementation(qual), kind, loc, return_type,
                prms, body, false, _ghost,
                is_variadic, templateExtension,
                false /* has_further_definition */,
                opt_none () /* throws */,
                contract);
            translation_unit_decl funcBare = NULL;
            if (bodyBare) {
              decl_or_impl_name bareDecl =
                decl_or_impl_name_dup(func->cons_translation_unit_decl
                  .Function.fun_name);
              _rttiTable.addBareToQualification(bareDecl
                  ->cons_decl_or_impl_name.Implementation.name);
              list /*arg_decl*/ prmsBare = NULL;
              if (prms) {
                ForwardReferenceList headerPrmsCopy(prmsBare);
                headerPrmsCopy.insertContainer(arg_decl_dup((arg_decl)
                  prms->element.container));
                list tmp = prms->next;
                while (tmp) {
                  headerPrmsCopy.insertContainer(arg_decl_dup((arg_decl)
                    tmp->element.container));
                  tmp = tmp->next;
                };
              };
              funcBare = translation_unit_decl_Function(
                bareDecl,
                funkind_dup(kind), copy_loc(loc),
                qual_type_dup(return_type),
                prmsBare,
                body->is_some ? bodyBare : opt_none(),
                false, _ghost, is_variadic,
                tkind_dup(templateExtension),
                false /* has_further_definition */,
                opt_none () /* throws */,
                contract->is_some
                  ? opt_some_container(function_contract_dup((function_contract)
                      contract->content.container))
                  : opt_none());
            };
            if (Decl->getDeclContext()->isRecord()) {
              assert(llvm::dyn_cast<clang::RecordDecl>(Decl->getDeclContext()));
              const clang::RecordDecl* outerRecord = 
                static_cast<const clang::RecordDecl*>(Decl->getDeclContext());
              while (outerRecord) {
                _tableForWaitingDeclarations.ensureGeneration(outerRecord,
                  waitDeclarations);
                const clang::DeclContext* parentDecl = outerRecord->getParent();
                clang::Decl::Kind kindDecl = parentDecl->getDeclKind();
                if (kindDecl >= clang::Decl::firstRecord
                    && kindDecl <= clang::Decl::lastRecord) {
                  assert(llvm::dyn_cast<clang::RecordDecl>(parentDecl));
                  outerRecord = static_cast<const clang::RecordDecl*>(
                      parentDecl);
                }
                else
                  outerRecord = NULL;
              };
            };
            _tableForWaitingDeclarations.addIncompleteFunction(
              Decl, waitDeclarations, func, funcBare);
            isGenerationEffective = false;
          }
        }
        else if (delayedBody && delayedBody->is_some /* && isInstance */) {
          std::vector<const clang::Decl*> waitDeclarations;
          popInstanceFunction(waitDeclarations);
          if (isInstance && Decl->getPrimaryTemplate())
            _clangUtils->popTemplateInstance(Decl->getPrimaryTemplate());
        };
        if (isGenerationEffective) {
          class_decl method = class_decl_CMethod(loc, name, kind, return_type,
            prms, is_variadic, body, is_implicit, templateExtension,
            false /* has_further_definition */,
            opt_none() /* throws */,
            contract);
          if (!contract->is_some) {
            _tableForWaitingDeclarations.addUpdateFunction(
              Decl,
              &method->cons_class_decl.CMethod.has_further_definition);
          };
          bool doesDuplicateMethod = true;
          if (!_clangUtils->isExternCContext(Decl)) {
            _parents.add(method);
            if (bodyBare && !delayedBody) {
              list /*arg_decl*/ prmsCopy = NULL;
              if (prms) {
                ForwardReferenceList headerPrmsCopy(prmsCopy);
                headerPrmsCopy.insertContainer(arg_decl_dup((arg_decl)
                  prms->element.container));
                list tmp = prms->next;
                while (tmp) {
                  headerPrmsCopy.insertContainer(arg_decl_dup((arg_decl)
                    tmp->element.container));
                  tmp = tmp->next;
                };
              };
              class_decl methodBare = class_decl_CMethod(copy_loc(loc),
                strdup(name),
                funkind_dup(kind),
                qual_type_dup(return_type),
                prmsCopy,
                is_variadic, opt_none(),
                false /* is_implicit */, tkind_dup(templateExtension),
                false /* has_further_definition */,
                opt_none() /* throws */,
                contract->is_some
                  ? opt_some_container(function_contract_dup((function_contract)
                      contract->content.container))
                  : opt_none());
              translation_unit_decl funcBare =_tableForWaitingDeclarations
                .globalizeDecl(Decl, methodBare);
              decl_or_impl_name bareDecl =
                funcBare->cons_translation_unit_decl.Function.fun_name;
              _rttiTable.addBareToQualification(bareDecl
                ->cons_decl_or_impl_name.Implementation.name);
              addDelayedImplementation(funcBare, Decl, strdup(name),
                  bodyBare);
            };
          }
          else if (!delayedBody) {
            assert(!bodyBare);
            doesDuplicateMethod = false;
            delayedBody = body;
            method->cons_class_decl.CMethod.body = opt_none();
            body = NULL;
          };
          if (delayedBody) {
            class_decl method_definition = doesDuplicateMethod
              ? class_decl_dup(method) : method;
            method_definition->cons_class_decl.CMethod.is_implicit = false;
            assert(!bodyBare || doesDuplicateMethod);
            method_definition->cons_class_decl.CMethod.is_implicit
              = is_implicit && !delayedBody;
            addDelayedImplementation(_tableForWaitingDeclarations
              .globalizeDecl(Decl, method_definition), Decl, name, delayedBody,
                 bodyBare);
          };
        } // isGenerationEffective = false
        else {
          assert(!delayedBody);
          list /*arg_decl*/ copyPrms = NULL;
          list /*arg_decl*/* endCopyPrms = &copyPrms;
          list prmsCursor = prms;
          while (prmsCursor) {
            (*endCopyPrms) = cons_container(arg_decl_dup((arg_decl)
              prmsCursor->element.container), NULL);
            endCopyPrms = &(*endCopyPrms)->next;
            prmsCursor = prmsCursor->next;
          };
          class_decl method = class_decl_CMethod(copy_loc(loc),
            strdup(name), funkind_dup(kind), qual_type_dup(return_type),
            copyPrms, is_variadic, opt_none(), is_implicit,
            tkind_dup(templateExtension), false /* has_further_definition */,
            opt_none() /* throws */, opt_none());
          _parents.add(method);
          if (bodyBare) {
            list /*arg_decl*/ prmsBare = NULL;
            if (prms) {
              ForwardReferenceList headerPrmsCopy(prmsBare);
              headerPrmsCopy.insertContainer(arg_decl_dup((arg_decl)
                prms->element.container));
              list tmp = prms->next;
              while (tmp) {
                headerPrmsCopy.insertContainer(arg_decl_dup((arg_decl)
                  tmp->element.container));
                tmp = tmp->next;
              };
            };
            class_decl methodBare = class_decl_CMethod(copy_loc(loc),
              strdup(name),
              funkind_dup(kind),
              qual_type_dup(return_type),
              prmsBare,
              is_variadic, opt_none(),
              is_implicit, tkind_dup(templateExtension),
              false /* has_further_definition */,
              opt_none() /* throws */,
              opt_none());
            translation_unit_decl funcBare =_tableForWaitingDeclarations
              .globalizeDecl(Decl, methodBare);
            decl_or_impl_name bareDecl =
              funcBare->cons_translation_unit_decl.Function.fun_name;
            _rttiTable.addBareToQualification(bareDecl
              ->cons_decl_or_impl_name.Implementation.name);
            addDelayedImplementation(funcBare, Decl, strdup(name),
                bodyBare);
          };
        }
      }
      else {
        qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
        free(const_cast<char*>(qual->decl_name));
        qual->decl_name = name;
        decl_or_impl_name decl_name = decl_or_impl_name_Implementation(qual);
        if (bodyBare) {
          body = delayedBody;
          delayedBody = NULL;
        };
        translation_unit_decl func =
          translation_unit_decl_Function(
            decl_name, kind, loc, return_type, prms, body,
            false, _ghost, is_variadic,
            templateExtension,
            false /* has_further_definition */,
            opt_none() /*throws*/,
            contract);
        translation_unit_decl funcBare = NULL;
        if (bodyBare) {
          list /*arg_decl*/ prmsBare = NULL;
          if (prms) {
            ForwardReferenceList headerPrmsCopy(prmsBare);
            headerPrmsCopy.insertContainer(arg_decl_dup((arg_decl)
              prms->element.container));
            list tmp = prms->next;
            while (tmp) {
              headerPrmsCopy.insertContainer(arg_decl_dup((arg_decl)
                tmp->element.container));
              tmp = tmp->next;
            };
          };
          funcBare =
            translation_unit_decl_Function(
              decl_or_impl_name_dup(decl_name), funkind_dup(kind),
              copy_loc(loc), qual_type_dup(return_type), prmsBare, bodyBare,
              false, NULL, is_variadic,
              tkind_dup(templateExtension),
              false /* has_further_definition */,
              opt_none() /*throws*/,
              opt_none());
          decl_or_impl_name bareDecl =
            funcBare->cons_translation_unit_decl.Function.fun_name;
          _rttiTable.addBareToQualification(bareDecl
            ->cons_decl_or_impl_name.Implementation.name);
        };
        if (!contract->is_some) {
          _tableForWaitingDeclarations.addUpdateFunction(
            Decl,
            &func->cons_translation_unit_decl.Function.has_further_definition);
        };
        if (body->is_some /* && isInstance */) {
          std::vector<const clang::Decl*> waitDeclarations;
          popInstanceFunction(waitDeclarations);
          if (isInstance && Decl->getPrimaryTemplate())
            _clangUtils->popTemplateInstance(Decl->getPrimaryTemplate());
          if (!waitDeclarations.empty()) {
            if (!qual->prequalification) {
              qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
              free(const_cast<char*>(qual->decl_name));
              qual->decl_name = name;
              decl_name = decl_or_impl_name_Implementation(qual);
            };
            _tableForWaitingDeclarations.addIncompleteFunction(Decl,
                waitDeclarations, func);
            isGenerationEffective = false;
          }
        }
        else if (!body->is_some && Decl->getTemplateSpecializationKind()
              >= clang::TSK_ImplicitInstantiation
            && !_tableForWaitingDeclarations.hasGenerated(current_class)) {
          if (!qual->prequalification) {
            qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
            free(const_cast<char*>(qual->decl_name));
            qual->decl_name = name;
            decl_name = decl_or_impl_name_Implementation(qual);
          };
          std::vector<const clang::Decl*> waitDeclarations;
          _tableForWaitingDeclarations.ensureGeneration(current_class,
            waitDeclarations);
          _tableForWaitingDeclarations.addIncompleteFunction(Decl,
              waitDeclarations, func);
          isGenerationEffective = false;
        }
        else if (delayedBody && delayedBody->is_some /* && isInstance */) {
          std::vector<const clang::Decl*> waitDeclarations;
          popInstanceFunction(waitDeclarations);
          if (isInstance && Decl->getPrimaryTemplate())
            _clangUtils->popTemplateInstance(Decl->getPrimaryTemplate());
        };
        if (isGenerationEffective) {
          if (_parents.hasLexicalContext()) {
            if (funcBare)
              _parents.add(funcBare);
            _parents.add(func);
          }
          else {
            if (funcBare)
              _globals.insertContainer(funcBare);
            _globals.insertContainer(func);
          };
          if (delayedBody)
            addDelayedImplementation(translation_unit_decl_dup(func),
                Decl, name, delayedBody);
        }
        else
          assert(!delayedBody);
      };
    }
    else {
      assert(!delayedBody);
      assert(Decl->getDeclContext()->isNamespace() /*_parents.isNamespace() */);
      decl_or_impl_name decl_name = NULL;
      if (Decl->getDeclContext() == Decl->getLexicalDeclContext())
        decl_name = decl_or_impl_name_Declaration(name);
      else {
        qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
        free(const_cast<char*>(qual->decl_name));
        qual->decl_name = name;
        decl_name = decl_or_impl_name_Implementation(qual);
      };
      translation_unit_decl func =
        translation_unit_decl_Function(
          decl_name, funkind_FKFunction(), loc, return_type, prms, body,
          false, _ghost, Decl->isVariadic(), templateExtension,
          false /* has_further_definition */,
          opt_none() /* throws */,
          contract);
      if (!contract->is_some) {
        _tableForWaitingDeclarations.addUpdateFunction(
          Decl,
          &func->cons_translation_unit_decl.Function.has_further_definition);
      };
      if (body->is_some /* && isInstance */) {
        std::vector<const clang::Decl*> waitDeclarations;
        popInstanceFunction(waitDeclarations);
        if (isInstance && Decl->getPrimaryTemplate())
          _clangUtils->popTemplateInstance(Decl->getPrimaryTemplate());
        if (!waitDeclarations.empty()) {
          //
          // The code below was commented out in order to allow analysis for a
          // widely used C++ construct. For the moment, it might be useful to
          // leave it here, so the approach can be revisited easily. Please find
          // more details in the bugtracker:
          // https://git.frama-c.com/pub/frama-c/-/issues/2564
          //
          // It appears that it was the intention to avoid duplicate definitions
          // in the output AST and instead only emit declarations for first
          // occurences. However, this also caused the frama-c engine to
          // generate default definitions for such first occurences and ignore
          // the actual implementations later on.
          //
          // The duplicate definitions don't seem harmful and the test suite
          // still works well. Analysis will use only one of them and report
          // the other one as uncovered.
          //
          //func->cons_translation_unit_decl.Function.body = opt_none();
          //translation_unit_decl copyFunc = translation_unit_decl_dup(func);
          //free(copyFunc->cons_translation_unit_decl.Function.body);
          //copyFunc->cons_translation_unit_decl.Function.body = body;
          if (_parents.hasLexicalContext() && !_parents.isClass())
            _parents.add(func);
          else {
            _globals.insertContainer(func);
          };
          //if (decl_name->tag_decl_or_impl_name == DECLARATION) {
          //  decl_name->cons_decl_or_impl_name.Declaration.name = strdup("");
          //  qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
          //  free(const_cast<char*>(qual->decl_name));
          //  qual->decl_name = name;
          //  free_decl_or_impl_name(decl_name);
          //  decl_name = decl_or_impl_name_Implementation(qual);
          //};
          _tableForWaitingDeclarations.addIncompleteFunction(Decl,
              waitDeclarations, func);
          isGenerationEffective = false;
        }
      };
      if (isGenerationEffective) {
        if (_parents.hasLexicalContext() && !_parents.isClass()
          /* to avoid instantiation of friend functions */)
          _parents.add(func);
        else {
          _globals.insertContainer(func);
        };
      };
    };
  };
  // _parents.clearLocalPush();

  // comment the test if needed (see VisitTypedef)
  if (isGenerationEffective) {
    if (_parents.hasLexicalContext())
      _tableForWaitingDeclarations.addFunctionDeclaration(Decl, _globals);
    else
      _tableForWaitingDeclarations.addDeclaration(Decl, _globals);
    _instanceContexts.removeUnvisited(Decl);
  };
  if (isNewTemplate && _templateCommentIndex >= -1)
    _templateCommentIndex = -2;

  return true;
}

void FramacVisitor::handleLexicalPostVisit(
  const clang::DeclContext* currentContext) {
  int templateContextsNumber = _templateContextsNumber;
  if (currentContext && currentContext != _lexicalContextForPostVisit) {
    const clang::DeclContext* newContext = NULL;
    if (currentContext->isNamespace() || currentContext->isRecord())
      newContext = currentContext;
    int currentDepth = 0;
    const clang::DeclContext* iteratorContext = currentContext;
    while (iteratorContext && iteratorContext != _lexicalContextForPostVisit) {
      if (!newContext && (iteratorContext->isNamespace()
            || iteratorContext->isRecord()))
        newContext = iteratorContext;
      iteratorContext = iteratorContext->getLexicalParent();
      ++currentDepth;
    };
    if (iteratorContext == _lexicalContextForPostVisit) {
      if (newContext && newContext != _lexicalContextForPostVisit) {
        while (newContext != _lexicalContextForPostVisit) {
          const clang::DeclContext* lastContext = newContext;
          iteratorContext = newContext;
          while (iteratorContext != _lexicalContextForPostVisit) {
            if (iteratorContext->isNamespace() || iteratorContext->isRecord())
              lastContext = iteratorContext;
            iteratorContext = iteratorContext->getLexicalParent();
          };
          if (lastContext->isNamespace()) {
            assert(llvm::dyn_cast<clang::NamespaceDecl>(lastContext));
            localLexicalVisitNamespaceDecl(static_cast<clang::NamespaceDecl*>(
                const_cast<clang::DeclContext*>(lastContext)));
          }
          else if (lastContext->isRecord()) {
            assert(llvm::dyn_cast<clang::RecordDecl>(lastContext));
            localLexicalVisitRecordDecl(static_cast<clang::RecordDecl*>(
                const_cast<clang::DeclContext*>(lastContext)));
          };
          _lexicalContextForPostVisit = lastContext;
          clang::Decl::Kind declKind
              = _lexicalContextForPostVisit->getDeclKind();
          if (((declKind == clang::Decl::Namespace)
                || (declKind == clang::Decl::LinkageSpec)
                || (declKind == clang::Decl::TranslationUnit))
              && _delayedImplementations.getFront())
            _globals.append(_delayedImplementations);
        }
      };
      return;
    };
    int synchroDepth = 0;
    const clang::DeclContext* synchroContext = _lexicalContextForPostVisit;
    while (synchroContext != NULL) {
      synchroContext = synchroContext->getLexicalParent();
      ++synchroDepth;
    };
    while (currentDepth > synchroDepth) {
      if (!newContext && (currentContext->isNamespace()
            || currentContext->isRecord()))
        newContext = currentContext;
      currentContext = currentContext->getLexicalParent();
      --currentDepth;
    };
    while (synchroDepth > currentDepth) {
      if (_lexicalContextForPostVisit->isNamespace()) {
        assert(llvm::dyn_cast<clang::NamespaceDecl>(
              _lexicalContextForPostVisit));
        postLexicalVisitNamespaceDecl(static_cast<clang::NamespaceDecl*>(
              const_cast<clang::DeclContext*>(_lexicalContextForPostVisit)));
      }
      else if (_lexicalContextForPostVisit->isRecord()) {
        assert(llvm::dyn_cast<clang::RecordDecl>(_lexicalContextForPostVisit));
        postLexicalVisitRecordDecl(static_cast<clang::RecordDecl*>(
            const_cast<clang::DeclContext*>(_lexicalContextForPostVisit)),
            templateContextsNumber);
      };
      --synchroDepth;
      _lexicalContextForPostVisit = _lexicalContextForPostVisit
          ->getLexicalParent();
      clang::Decl::Kind declKind = _lexicalContextForPostVisit->getDeclKind();
      if (((declKind == clang::Decl::Namespace)
            || (declKind == clang::Decl::LinkageSpec)
            || (declKind == clang::Decl::TranslationUnit))
          && _delayedImplementations.getFront())
        _globals.append(_delayedImplementations);
    };
    while (currentContext != _lexicalContextForPostVisit) {
      if (!newContext && (currentContext->isNamespace()
            || currentContext->isRecord()))
        newContext = currentContext;
      if (_lexicalContextForPostVisit->isNamespace()) {
        assert(llvm::dyn_cast<clang::NamespaceDecl>
            (_lexicalContextForPostVisit));
        postLexicalVisitNamespaceDecl(static_cast<clang::NamespaceDecl*>(
              const_cast<clang::DeclContext*>(_lexicalContextForPostVisit)));
      }
      else if (_lexicalContextForPostVisit->isRecord()) {
        assert(llvm::dyn_cast<clang::RecordDecl>(_lexicalContextForPostVisit));
        postLexicalVisitRecordDecl(static_cast<clang::RecordDecl*>(
            const_cast<clang::DeclContext*>(_lexicalContextForPostVisit)),
            templateContextsNumber);
      };
      currentContext = currentContext->getLexicalParent();
      _lexicalContextForPostVisit = _lexicalContextForPostVisit->getLexicalParent();
      clang::Decl::Kind declKind = _lexicalContextForPostVisit->getDeclKind();
      if (((declKind == clang::Decl::Namespace)
            || (declKind == clang::Decl::LinkageSpec)
            || (declKind == clang::Decl::TranslationUnit))
          && _delayedImplementations.getFront())
        _globals.append(_delayedImplementations);
    };
    if (newContext && !_lexicalContextForPostVisit->isExternCContext()) {
      // _lexicalContextForPostVisit == newContext;
      while (newContext != _lexicalContextForPostVisit) {
        const clang::DeclContext* lastContext = newContext;
        iteratorContext = newContext;
        while (iteratorContext != _lexicalContextForPostVisit) {
          if (iteratorContext->isNamespace() || iteratorContext->isRecord())
            lastContext = iteratorContext;
          iteratorContext = iteratorContext->getLexicalParent();
        };
        if (lastContext->isNamespace()) {
          assert(llvm::dyn_cast<clang::NamespaceDecl>(lastContext));
          localLexicalVisitNamespaceDecl(static_cast<clang::NamespaceDecl*>(
              const_cast<clang::DeclContext*>(lastContext)));
        }
        else if (lastContext->isRecord()) {
          assert(llvm::dyn_cast<clang::RecordDecl>(lastContext));
          localLexicalVisitRecordDecl(static_cast<clang::RecordDecl*>(
              const_cast<clang::DeclContext*>(lastContext)));
        };
        _lexicalContextForPostVisit = lastContext;
        clang::Decl::Kind declKind = _lexicalContextForPostVisit->getDeclKind();
        if (((declKind == clang::Decl::Namespace)
              || (declKind == clang::Decl::LinkageSpec)
              || (declKind == clang::Decl::TranslationUnit))
            && _delayedImplementations.getFront())
          _globals.append(_delayedImplementations);
      }
    }
  };
}

void FramacVisitor::handleSemanticPostVisit(
  const clang::DeclContext* currentContext) {
  if (currentContext && currentContext != _semanticContextForPostVisit) {
    const clang::DeclContext* newContext = NULL;
    if (currentContext->isNamespace() || currentContext->isRecord())
      newContext = currentContext;
    int currentDepth = 0;
    const clang::DeclContext* iteratorContext = currentContext;
    while (iteratorContext && iteratorContext != _semanticContextForPostVisit) {
      if (!newContext && (iteratorContext->isNamespace()
            || iteratorContext->isRecord()))
        newContext = iteratorContext;
      iteratorContext = iteratorContext->getParent();
      ++currentDepth;
    };
    if (iteratorContext == _semanticContextForPostVisit) {
      if (newContext && newContext != _semanticContextForPostVisit) {
        while (newContext != _semanticContextForPostVisit) {
          const clang::DeclContext* lastContext = newContext;
          iteratorContext = newContext;
          while (iteratorContext != _semanticContextForPostVisit) {
            if (iteratorContext->isNamespace() || iteratorContext->isRecord())
              lastContext = iteratorContext;
            iteratorContext = iteratorContext->getParent();
          };
          if (lastContext->isNamespace()) {
            assert(llvm::dyn_cast<clang::NamespaceDecl>(lastContext));
            localSemanticVisitNamespaceDecl(static_cast<clang::NamespaceDecl*>(
                const_cast<clang::DeclContext*>(lastContext)));
          }
          else if (lastContext->isRecord()) {
            assert(llvm::dyn_cast<clang::RecordDecl>(lastContext));
            const clang::CXXRecordDecl *RD
              = llvm::dyn_cast<clang::CXXRecordDecl>(lastContext);
            if (RD && (RD->getDescribedClassTemplate()
                && (RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)))
            { pushTemplateContext();
              _state = (State) (_state | STemplateSynchronized);
            }
            else if (RD && (RD->getKind()
                    == clang::Decl::ClassTemplatePartialSpecialization)) {
              pushTemplateContext();
              _state = (State) (_state | STemplateSynchronized);
            };
            localSemanticVisitRecordDecl(static_cast<clang::RecordDecl*>(
                const_cast<clang::DeclContext*>(lastContext)));
          };
          _semanticContextForPostVisit = lastContext;
        }
      };
      return;
    };
    int synchroDepth = 0;
    const clang::DeclContext* synchroContext = _semanticContextForPostVisit;
    while (synchroContext != NULL) {
      synchroContext = synchroContext->getParent();
      ++synchroDepth;
    };
    while (currentDepth > synchroDepth) {
      if (!newContext && (currentContext->isNamespace()
            || currentContext->isRecord()))
        newContext = currentContext;
      currentContext = currentContext->getParent();
      --currentDepth;
    };
    while (synchroDepth > currentDepth) {
      if (_semanticContextForPostVisit->isNamespace()) {
        assert(llvm::dyn_cast<clang::NamespaceDecl>(
              _semanticContextForPostVisit));
        postSemanticVisitNamespaceDecl(static_cast<clang::NamespaceDecl*>(
              const_cast<clang::DeclContext*>(_semanticContextForPostVisit)));
      }
      else if (_semanticContextForPostVisit->isRecord()) {
        assert(llvm::dyn_cast<clang::RecordDecl>(_semanticContextForPostVisit));
        const clang::CXXRecordDecl *RD
          = llvm::dyn_cast<clang::CXXRecordDecl>(_semanticContextForPostVisit);
        if (RD && RD->getDescribedClassTemplate()
            && (RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)) {
          if (RD->getDescribedClassTemplate()->isThisDeclarationADefinition()
              || _parents.isSemanticLocalClass()) {
            assert(_state >= STemplateSynchronized);
            popTemplateContext();
            // done by postSemanticVisitRecordDecl
            // if (!hasTemplateContext()) {
            //   _state = (State) (_state & 0x3);
            //   if (hasInstanceContext())
            //     _state = (State) (_state | SInstanceSynchronized);
            // };
          }
        }
        else if (RD
            && RD->getKind() == clang::Decl::ClassTemplatePartialSpecialization
            && (RD->isThisDeclarationADefinition()
                || _parents.isSemanticLocalClass())) {
          assert(_state >= STemplateSynchronized);
          popTemplateContext();
          // done by postSemanticVisitRecordDecl
          // if (!hasTemplateContext()) {
          //   _state = (State) (_state & 0x3);
          //   if (hasInstanceContext())
          //     _state = (State) (_state | SInstanceSynchronized);
          // }
        }
        else {
          clang::Decl::Kind declKind = RD->getDeclContext()->getDeclKind();
          if ((declKind >= clang::Decl::firstFunction
                && declKind <= clang::Decl::lastFunction)) {
            if (static_cast<const clang::FunctionDecl*>(RD->getDeclContext())
                ->getTemplatedKind()==clang::FunctionDecl::TK_FunctionTemplate)
            { assert(_state >= STemplateSynchronized);
              popTemplateContext();
              // done by postSemanticVisitRecordDecl
              // if (!hasTemplateContext()) {
              //   _state = (State) (_state & 0x3);
              //   if (hasInstanceContext())
              //     _state = (State) (_state | SInstanceSynchronized);
              // };
            }
          };
        };

        // else if (RD && RD->getKind() // done by postSemanticVisitRecordDecl!
        //     == clang::Decl::ClassTemplateSpecialization) {
        //   // do not handle partial specialization !
        //   const clang::ClassTemplateSpecializationDecl* TSD
        //     = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(RD);
        //   if (TSD && TSD->isThisDeclarationADefinition() &&
        //       isTemplateInstance(RD->getTemplateSpecializationKind())) {
        //     assert(_state >= SInstanceSynchronized);
        //     popInstanceContext(RD);
        //     if (!hasInstanceContext())
        //       _state = (State) (_state & 0x3);
        //     _clangUtils->popTemplateInstance(TSD->getSpecializedTemplate());
        //   }
        // };
        postSemanticVisitRecordDecl(static_cast<clang::RecordDecl*>(
            const_cast<clang::DeclContext*>(_semanticContextForPostVisit)));
      };
      --synchroDepth;
      _semanticContextForPostVisit = _semanticContextForPostVisit->getParent();
    };
    while (currentContext != _semanticContextForPostVisit) {
      if (!newContext && (currentContext->isNamespace()
            || currentContext->isRecord()))
        newContext = currentContext;
      if (_semanticContextForPostVisit->isNamespace()) {
        assert(llvm::dyn_cast<clang::NamespaceDecl>
            (_semanticContextForPostVisit));
        postSemanticVisitNamespaceDecl(static_cast<clang::NamespaceDecl*>(
              const_cast<clang::DeclContext*>(_semanticContextForPostVisit)));
      }
      else if (_semanticContextForPostVisit->isRecord()) {
        assert(llvm::dyn_cast<clang::RecordDecl>(_semanticContextForPostVisit));
        const clang::CXXRecordDecl *RD
          = llvm::dyn_cast<clang::CXXRecordDecl>(_semanticContextForPostVisit);
        if (RD && RD->getDescribedClassTemplate()
            && (RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)) {
          if (RD->getDescribedClassTemplate()->isThisDeclarationADefinition()
              || _parents.isSemanticLocalClass()) {
            assert(_state >= STemplateSynchronized);
            popTemplateContext();
            // done by postSemanticVisitRecordDecl
            // if (!hasTemplateContext()) {
            //   _state = (State) (_state & 0x3);
            //   if (hasInstanceContext())
            //     _state = (State) (_state | SInstanceSynchronized);
            // };
          }
        }
        else if (RD
            && RD->getKind() == clang::Decl::ClassTemplatePartialSpecialization
            && (RD->isThisDeclarationADefinition()
                || _parents.isSemanticLocalClass())) {
          assert(_state >= STemplateSynchronized);
          popTemplateContext();
          // done by postSemanticVisitRecordDecl
          // if (!hasTemplateContext()) {
          //   _state = (State) (_state & 0x3);
          //   if (hasInstanceContext())
          //     _state = (State) (_state | SInstanceSynchronized);
          // }
        }
        // else if (RD && RD->getKind()
        //     == clang::Decl::ClassTemplateSpecialization) {
        //   // do not handle partial specialization !
        //   const clang::ClassTemplateSpecializationDecl* TSD
        //     = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(RD);
        //   if (TSD && TSD->isThisDeclarationADefinition() &&
        //       isTemplateInstance(RD->getTemplateSpecializationKind())) {
        //     assert(_state >= SInstanceSynchronized);
        //     popInstanceContext(RD);
        //     if (!hasInstanceContext())
        //       _state = (State) (_state & 0x3);
        //     _clangUtils->popTemplateInstance(TSD->getSpecializedTemplate());
        //   }
        // };
        postSemanticVisitRecordDecl(static_cast<clang::RecordDecl*>(
            const_cast<clang::DeclContext*>(_semanticContextForPostVisit)));
      };
      currentContext = currentContext->getParent();
      _semanticContextForPostVisit = _semanticContextForPostVisit->getParent();
    };
    if (newContext && !_semanticContextForPostVisit->isExternCContext()) {
      // _semanticContextForPostVisit == newContext;
      while (newContext != _semanticContextForPostVisit) {
        const clang::DeclContext* lastContext = newContext;
        iteratorContext = newContext;
        while (iteratorContext != _semanticContextForPostVisit) {
          if (iteratorContext->isNamespace() || iteratorContext->isRecord())
            lastContext = iteratorContext;
          iteratorContext = iteratorContext->getParent();
        };
        if (lastContext->isNamespace()) {
          assert(llvm::dyn_cast<clang::NamespaceDecl>(lastContext));
          localSemanticVisitNamespaceDecl(static_cast<clang::NamespaceDecl*>(
              const_cast<clang::DeclContext*>(lastContext)));
        }
        else if (lastContext->isRecord()) {
          assert(llvm::dyn_cast<clang::RecordDecl>(lastContext));
          const clang::CXXRecordDecl *RD
            = llvm::dyn_cast<clang::CXXRecordDecl>(lastContext);
          if (RD && RD->getDescribedClassTemplate()
              && (RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)) {
            pushTemplateContext();
            _state = (State) (_state | STemplateSynchronized);
          }
          else if (RD && (RD->getKind()
                  == clang::Decl::ClassTemplatePartialSpecialization)) {
            pushTemplateContext();
            _state = (State) (_state | STemplateSynchronized);
          }
          localSemanticVisitRecordDecl(static_cast<clang::RecordDecl*>(
              const_cast<clang::DeclContext*>(lastContext)));
        };
        _semanticContextForPostVisit = lastContext;
      }
    }
  };
}

bool FramacVisitor::localLexicalVisitNamespaceDecl(clang::NamespaceDecl* Decl)
{ // assert(false); // it occurs with specialization outside namespace
  const char* name;
  if (!_parents.hasLexicalContext())
    name = copy_string(Decl->getQualifiedNameAsString());
  else
    name = copy_string(Decl->getName().str());
  location loc = makeLocation(Decl->getSourceRange());
  translation_unit_decl namespaceDecl =
    translation_unit_decl_Namespace(loc, name, NULL);
  if (!_parents.hasLexicalContext()) {
    _globals.insertContainer(namespaceDecl);
  }
  else {
    assert(_parents.isNamespace());
    _parents.add(namespaceDecl);
  };
  assert(_state == SSynchronized);
  _parents.pushNamespace(
    namespaceDecl->cons_translation_unit_decl.Namespace.body, Decl);
  // _parents.pushLexicalLocalNamespace(Decl);
  return true;
}

bool FramacVisitor::localSemanticVisitNamespaceDecl(clang::NamespaceDecl* Decl)
{ assert(_state <= STempLexicalOut);
  _parents.pushSemanticLocalNamespace(Decl);
  // _state = STempLexicalOut;
  _semanticContextForPostVisit = Decl;
  return true;
}

bool FramacVisitor::TraverseLinkageSpecDecl(clang::LinkageSpecDecl* Decl) {
  bool res = Parent::TraverseLinkageSpecDecl(Decl);
  handlePostVisit(Decl, Decl);
  readGlobalCommentUntil(_clangUtils->getEndLoc(*Decl), Decl, false);
  return res;
}

bool FramacVisitor::TraverseNamespaceDecl(clang::NamespaceDecl* Decl) {
  bool res = Parent::TraverseNamespaceDecl(Decl);
  handlePostVisit(Decl->getLexicalDeclContext(), Decl->getParent());
  readGlobalCommentUntil(_clangUtils->getEndLoc(*Decl), Decl, false);
  return res;
}

bool FramacVisitor::VisitNamespaceDecl(clang::NamespaceDecl* Decl) {
  if (!_ghost && isGhostDecl(Decl)) return true;
  handlePostVisit(Decl->getLexicalDeclContext(), Decl->getParent());
  _lexicalContextForPostVisit = Decl;
  _semanticContextForPostVisit = Decl;
  readGlobalComment(Decl, false /* mayHaveTemplate */);
  const char* name;
  if (!_parents.hasLexicalContext())
    name = copy_string(Decl->getQualifiedNameAsString());
  else
    name = copy_string(Decl->getName().str());
  location loc = makeLocation(Decl->getSourceRange());
  translation_unit_decl namespaceDecl =
    translation_unit_decl_Namespace(loc, name, NULL);
  if (!_parents.hasLexicalContext()) _globals.insertContainer(namespaceDecl);
  else {
    assert(_parents.isNamespace());
    _parents.add(namespaceDecl);
  };
  assert(_state == SSynchronized);
  _parents.pushNamespace(
    namespaceDecl->cons_translation_unit_decl.Namespace.body, Decl);
  return true;
}

void FramacVisitor::postLexicalVisitNamespaceDecl(clang::NamespaceDecl* Decl) {
  if (!_parents.hasLexicalLocalContext(Decl))
    readGlobalComment(Decl, false /* mayHaveTemplate */);
  // assert(_state == SSynchronized);
  // the case STempLexicalOut occurs because postSemanticVisitNamespaceDecl
  //   has not still been called.
  _parents.lexicalSynchronizeWith(Decl->getLexicalDeclContext(), *this);
}

void FramacVisitor::postSemanticVisitNamespaceDecl(clang::NamespaceDecl* Decl) {
  // assert(_state == SSynchronized);
  // some local states may be in inner unsynchronized classes.
  _parents.semanticSynchronizeWith(Decl->getParent(), *this);
  assert(_state == SSynchronized);
}

bool FramacVisitor::VisitEnumDecl(clang::EnumDecl* Decl) {
  if (!_ghost && isGhostDecl(Decl)) return true;
  { clang::Decl::Kind declKind = Decl->getDeclContext()->getDeclKind();
    if ((declKind >= clang::Decl::firstFunction
          && declKind <= clang::Decl::lastFunction)
        && (static_cast<const clang::FunctionDecl*>(Decl->getDeclContext())
            ->getTemplatedKind() == clang::FunctionDecl::TK_FunctionTemplate))
      return true;
  }
  if (/* _parents. */ hasTemplateContext()) {
    if (_parents.isSemanticLocalClass())
      handleSemanticPostVisit(Decl->getDeclContext());
    else
      handlePostVisit(Decl->getLexicalDeclContext(), Decl->getDeclContext());
    registerTemplateDecl(Decl);
    return true;
  };
  handlePostVisit(Decl->getLexicalDeclContext(), Decl->getDeclContext());
  readGlobalComment(Decl, true /* mayHaveTemplate */);
  qualified_name enumName = _clangUtils->makeQualifiedName(*Decl);
  bool isFirstEnumName = true;
  bool isExternC = Clang_utils::isExternCContext(Decl);
  const char* name = strdup(enumName->decl_name);
  // if (!_parents.hasLexicalContext())
  //   name = copy_string(Decl->getQualifiedNameAsString());
  // else
  //   name = copy_string(Decl->getName().str());
  location loc = makeLocation(Decl->getSourceRange());
  list /* compilation_constant */ enums = NULL;
  ForwardReferenceList forwardEnums(enums);
  clang::EnumDecl::enumerator_iterator enumEnd = Decl->enumerator_end();
  for (clang::EnumDecl::enumerator_iterator enumIter = Decl->enumerator_begin();
      enumIter != enumEnd; ++enumIter) {
    qualified_name itemName = _clangUtils->makeQualifiedName(**enumIter);
    compilation_constant newEnum =
      compilation_constant_EnumCst(
        itemName,
        ekind_cons(
          isFirstEnumName ? enumName : qualified_name_dup(enumName),isExternC),
        (int64_t) enumIter->getInitVal().getLimitedValue(UINT64_MAX));
    isFirstEnumName = false;
    forwardEnums.insertContainer(newEnum);
  };
  if (isFirstEnumName)
    free_qualified_name(enumName);
  clang::QualType repr = Decl->getIntegerType();
  assert (repr->isIntegerType());
  ikind kind = _clangUtils->makeIntConstantType(repr.getTypePtr());
  clang::Decl::Kind declKind = Decl->getDeclContext()->getDeclKind();
  if (declKind == clang::Decl::TranslationUnit
      || declKind == clang::Decl::LinkageSpec
      /* !_parents.hasLexicalContext() */) {
    decl_or_impl_name decl_name = NULL;
    if (Decl->getDeclContext() == Decl->getLexicalDeclContext())
      decl_name = decl_or_impl_name_Declaration(name);
    else {
      qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
      free(const_cast<char*>(qual->decl_name));
      qual->decl_name = name;
      decl_name = decl_or_impl_name_Implementation(qual);
    };
    translation_unit_decl decl =
      translation_unit_decl_EnumDecl(
        loc, decl_name, kind, opt_some_container(enums),
        Clang_utils::isExternCContext(Decl),_ghost);
    _globals.insertContainer(decl);
  }
  else {
    if (Decl->getDeclContext()->isRecord() /* _parents.isClass()*/) {
      if (_parents.isClass()) {
        class_decl decl = class_decl_CEnum(loc, name, kind,
          opt_some_container(enums));
        _parents.add(decl);
      }
      else {
        qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
        free(const_cast<char*>(qual->decl_name));
        qual->decl_name = name;
        decl_or_impl_name decl_name = decl_or_impl_name_Implementation(qual);
        translation_unit_decl decl =
          translation_unit_decl_EnumDecl(
            loc, decl_name, kind, opt_some_container(enums), false,_ghost);
        if (_parents.hasLexicalContext()) _parents.add(decl);
        else _globals.insertContainer(decl);
      };
    }
    else {
      assert(Decl->getDeclContext()->isNamespace() /*_parents.isNamespace() */);
      decl_or_impl_name decl_name = NULL;
      if (Decl->getDeclContext() == Decl->getLexicalDeclContext())
        decl_name = decl_or_impl_name_Declaration(name);
      else {
        qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
        free(const_cast<char*>(qual->decl_name));
        qual->decl_name = name;
        decl_name = decl_or_impl_name_Implementation(qual);
      };
      translation_unit_decl decl =
        translation_unit_decl_EnumDecl(
          loc, decl_name, kind, opt_some_container(enums), false,_ghost);
      if (_parents.hasLexicalContext()) _parents.add(decl);
      else _globals.insertContainer(decl);
    };
  };
  // _parents.clearLocalPush();
  _tableForWaitingDeclarations.addDeclaration(Decl, _globals);
  // _instanceContexts.removeUnvisited(Decl);
  return true;
}

bool FramacVisitor::localLexicalVisitRecordDecl(clang::RecordDecl* Decl) {
  if (Decl->isThisDeclarationADefinition()) {
    _parents.pushLexicalLocalClass(Decl);
  }
  else {
  location loc = makeLocation(Decl->getLocation());
  std::cerr << "Unsupported declaration without definition in " << 
    Decl->getName().str() <<
    " at " << loc->filename1 << ":" << loc -> linenum1 << 
    "," << loc->charnum1 << 
    std::endl ; 
  assert(false);
  };
  return true;
}

bool FramacVisitor::localSemanticVisitRecordDecl(clang::RecordDecl* Decl) {
  const clang::CXXRecordDecl *RD = llvm::dyn_cast<clang::CXXRecordDecl>(Decl);
  const clang::ClassTemplateSpecializationDecl* TSD = NULL;
  if (Decl->getKind() == clang::Decl::ClassTemplateSpecialization)
    // do not handle partial specialization !
    TSD = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(Decl);
  if (RD || /* _parents. */ hasTemplateContext()) {
    if ((/* _parents. */hasTemplateContext()
        || (RD->getDescribedClassTemplate()
            && RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)
        || (RD->getKind() == clang::Decl::ClassTemplatePartialSpecialization))
        && (!RD || !TSD || !isTemplateInstance(
            RD->getTemplateSpecializationKind())
         /* RD->getTemplateSpecializationKind()
              < clang::TSK_ImplicitInstantiation */)) {
      registerTemplateDecl(Decl);
      assert((_state & 0x3) <= STempLexicalOut);
      if (RD->getDescribedClassTemplate()
          && (RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)) {
        // We are going to visit the content of template records
        _parents.pushSemanticLocalTemplateClass(Decl);
        _state = (State) (_state | STempLexicalOut | STemplateSynchronized);
      }
      else {
        _parents.pushSemanticLocalClass(Decl);
        _state = (State) (_state | STempLexicalOut);
      };
      _semanticContextForPostVisit = Decl;
      // returning false stops the global visit instead of preventing
      //    nested visit.
      return true;
    };
  };
  assert((_state & 0x3) <= STempLexicalOut);
  _parents.pushSemanticLocalClass(Decl);
  _state = (State) (_state | STempLexicalOut);
  _semanticContextForPostVisit = Decl;

  if (RD && RD->getKind() == clang::Decl::ClassTemplateSpecialization
      && TSD
      && isTemplateInstance(RD->getTemplateSpecializationKind())) {
    // do not handle partial specialization !
    // const clang::ClassTemplateSpecializationDecl* TSD
    //    = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(RD);
    _clangUtils->pushTemplateInstance(TSD->getSpecializedTemplate(),
        &TSD->getTemplateArgs());
  }
  return true;
}

/* inheritance */ list FramacVisitor::makeInheritanceList(
  clang::CXXRecordDecl* cxxDecl,
  std::vector<const clang::Decl*>* unvisitedInstanceDecls,
  std::vector<const clang::CXXRecordDecl*>* unvisitedBases) {
  /* inheritance */ list bodyInherits = NULL;
  ForwardReferenceList forwardInherits(bodyInherits);
  clang::CXXRecordDecl::base_class_iterator endBase = cxxDecl->bases_end();
  for (clang::CXXRecordDecl::base_class_iterator
      iterBase = cxxDecl->bases_begin(); iterBase != endBase; ++iterBase) {
    const clang::Type* type = iterBase->getType().getTypePtr();
    const clang::CXXRecordDecl* base = type->getAsCXXRecordDecl();
    if (!base) {
      std::cerr << "Unsupported Inheritance Type:"
          << iterBase->getType().getAsString ()
          << "\nAborting\n";
      exit(2);
    };
    int derivationPosition = 0;
    derivationPosition= _rttiTable.addDerivation(base, iterBase->isVirtual());
    if (unvisitedInstanceDecls)
      _tableForWaitingDeclarations.ensureGeneration(base,
                                                    *unvisitedInstanceDecls);
    else if (unvisitedBases && !_tableForWaitingDeclarations.hasVisited(base))
      unvisitedBases->push_back(base);
    clang::RecordDecl::TagKind tagKind = base->getTagKind();
    qualified_name baseName = _clangUtils->makeQualifiedName(*base);
    if (tagKind != clang::TTK_Class && tagKind != clang::TTK_Struct) {
      std::cerr << "Unsupported Inheritance Type:"
          << iterBase->getType().getAsString ()
          << "\nAborting\n";
      exit(2);
    };
    tkind templateParameters = _clangUtils->makeTemplateKind(base);
    vkind virt = iterBase->isVirtual() ? VVIRTUAL: VSTANDARD;
    access_kind akind = access_kind(iterBase->getAccessSpecifier());
    forwardInherits.insertContainer(
      inheritance_cons(
        baseName, templateParameters, akind, virt, derivationPosition));
  };
  return bodyInherits;
}

bool
FramaCIRGenAction::ImmediateGlobalDependency::globalInsertIfBooked(
    const clang::RecordDecl* decl,
    const std::list<LexicalLocalDeclContext>* context, 
    translation_unit_decl globalDecl,
    /* translation_unit_decl */ list*& insertionPlace,
    bool isInClass, const FramacVisitor& visitor) {
  NamespaceContext thisContext;
  if (context) {
    std::list<LexicalLocalDeclContext>::const_iterator
      iterEnd = context->end(), iter;
    for (iter = context->begin(); iter != iterEnd; ++iter) {
      if (!isInClass || &*iter != &context->back()) {
        assert(llvm::dyn_cast<clang::NamespaceDecl>(iter->getSynchro()));
        thisContext.push_back(std::make_pair(
            static_cast<const clang::NamespaceDecl*>(iter->getSynchro()),
            iter->getNamespacePlace()));
      };
    };
  };

  std::vector<PlaceForDeclGeneration>::iterator
    iterEnd = _placesForDecl.end(), iter;
  bool result = false;
  for (iter = _placesForDecl.begin(); !result && iter != iterEnd; ++iter)
    if (iter->getClassDecl() == decl) {
      iter->adjustPlace();
      int insertionStackSize = iter->getNamespaceContext().size(),
          stackSize = thisContext.size();
      /* translation_unit_decl */ list* place = iter->getPlace();
      translation_unit_decl toInsert = NULL;
      while (insertionStackSize > stackSize) {
        --insertionStackSize;
        assert(*place);
        /* translation_unit_decl */ list next = *place;
        const clang::NamespaceDecl* namespaceDecl = 
          iter->getNamespaceContext()[insertionStackSize].first;
        translation_unit_decl newNamespace = translation_unit_decl_Namespace(
          visitor.makeLocation(namespaceDecl->getSourceRange()),
          copy_string(namespaceDecl->getNameAsString()), next);
        *place = NULL;
        place = iter->getNamespaceContext()[insertionStackSize].second;
        next = *place;
        *place = cons_container(newNamespace, next);
      };
      while (insertionStackSize < stackSize) {
        --stackSize;
        const clang::NamespaceDecl*
          namespaceDecl = thisContext[stackSize].first;
        toInsert = translation_unit_decl_Namespace(
          visitor.makeLocation(namespaceDecl->getSourceRange()),
          copy_string(namespaceDecl->getNameAsString()),
          cons_container(toInsert, NULL));
      };
      while (insertionStackSize > 0
        && iter->getNamespaceContext()[insertionStackSize-1].first !=
          thisContext[insertionStackSize-1].first) { 
        --insertionStackSize;
        --stackSize;
        assert(*place);
        /* translation_unit_decl */ list next = *place;
        const clang::NamespaceDecl* namespaceDecl = 
          iter->getNamespaceContext()[insertionStackSize].first;
        translation_unit_decl newNamespace = translation_unit_decl_Namespace(
          visitor.makeLocation(namespaceDecl->getSourceRange()),
          copy_string(namespaceDecl->getNameAsString()), next);
        *place = NULL;
        place = iter->getNamespaceContext()[insertionStackSize].second;
        next = *place;
        *place = cons_container(newNamespace, next);

        namespaceDecl = thisContext[stackSize].first;
        toInsert = translation_unit_decl_Namespace(
          visitor.makeLocation(namespaceDecl->getSourceRange()),
          copy_string(namespaceDecl->getNameAsString()),
          cons_container(toInsert, NULL));
      };
      assert(*place);
      insertionPlace = place;
      if (toInsert) {
        /* translation_unit_decl */ list next = *place;
        *place = cons_container(toInsert, next);
        while (toInsert->cons_translation_unit_decl.Namespace.body) {
          /* translation_unit_decl */ list body
            = toInsert->cons_translation_unit_decl.Namespace.body;
          assert(body && !body->next && ((translation_unit_decl)
            body->element.container)->tag_translation_unit_decl == NAMESPACE);
          toInsert = (translation_unit_decl) body->element.container;
        };
        place = &toInsert->cons_translation_unit_decl.Namespace.body;
      };

      /* translation_unit_decl */ list next = *place;
      *place = cons_container(globalDecl, next);
      _placesForDecl.erase(iter);
      result = true;
    };
  return result;
}

bool
FramaCIRGenAction::ImmediateGlobalDependency::hasGlobalBooked(
    const clang::RecordDecl* decl) const {
  std::vector<PlaceForDeclGeneration>::const_iterator
    iterEnd = _placesForDecl.end(), iter;
  bool result = false;
  for (iter = _placesForDecl.begin(); !result && iter != iterEnd; ++iter)
    if (iter->getClassDecl() == decl)
      result = true;
  return result;
}

/* translation_unit_decl */ list*
FramaCIRGenAction::ImmediateGlobalDependency::adjustBeforePlace(
    const clang::RecordDecl* decl) {
  std::vector<PlaceForDeclGeneration>::iterator
    iterEnd = _placesForDecl.end(), iter;
  /* translation_unit_decl */ list* result = NULL;
  for (iter = _placesForDecl.begin(); !result && iter != iterEnd; ++iter)
    if (iter->getClassDecl() == decl) {
      iter->setNextPlace();
      result = iter->getPlace();
    };
  return result;
}

void
FramaCIRGenAction::ImmediateGlobalDependency::makeTemporaryDependentUnvisited(
    const clang::RecordDecl* baseClass, VisitTable& visitTable) {
  std::vector<PlaceForDeclGeneration>::iterator
    iterEnd = _placesForDecl.end(), iter;
  bool result = false;
  for (iter = _placesForDecl.begin(); !result && iter != iterEnd; ++iter)
    if (iter->getClassDecl() == baseClass) {
      visitTable.makeTemporaryUnvisited(iter->getOriginClassDecl());
      result = true;
    };
  assert(result);
}

void
FramaCIRGenAction::ImmediateGlobalDependency::makeTemporaryDependentVisited(
    const clang::RecordDecl* baseClass, VisitTable& visitTable,
    ForwardReferenceList& globals) {
  std::vector<PlaceForDeclGeneration>::iterator
    iterEnd = _placesForDecl.end(), iter;
  bool result = false;
  for (iter = _placesForDecl.begin(); !result && iter != iterEnd; ++iter)
    if (iter->getClassDecl() == baseClass) {
      visitTable.makeTemporaryVisited(iter->getOriginClassDecl(), globals);
      result = true;
    };
  assert(result);
}

bool FramacVisitor::VisitRecordDecl(clang::RecordDecl* Decl) {
  const clang::CXXRecordDecl *RD = llvm::dyn_cast<clang::CXXRecordDecl>(Decl);
  if (RD && RD->isLambda()) return true; // Lambda is handled directly by IR
  if (RD && (RD->getKind() == clang::Decl::ClassTemplatePartialSpecialization))
    return true; // case handled by VisitClassTemplatePartialSpecializationDecl
  if (!_ghost && isGhostDecl(Decl)) return true;
  if (/* _parents. */ hasTemplateContext() && _parents.isSemanticLocalClass())
    handleSemanticPostVisit(Decl->getParent());
  else
    handlePostVisit(Decl->getLexicalDeclContext(), Decl->getParent());
  if (!hasTemplateContext() || !_parents.isSemanticLocalClass())
    _lexicalContextForPostVisit = Decl;
  _semanticContextForPostVisit = Decl;
  if (RD && RD->getDescribedClassTemplate()
      && (RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)) {
    if (RD->getDescribedClassTemplate()->isThisDeclarationADefinition()) {
      pushTemplateContext();
      _state = (State) (_state | STemplateSynchronized);
    }
  }
  
  const clang::ClassTemplateSpecializationDecl* TSD = NULL;
  if (Decl->getKind() == clang::Decl::ClassTemplateSpecialization)
    // do not handle partial specialization !
    TSD = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(Decl);
  if (RD || /* _parents. */ hasTemplateContext()) {
    if ((/* _parents. */hasTemplateContext()
        || (RD->getDescribedClassTemplate()
            && RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)
        || (RD->getKind() == clang::Decl::ClassTemplatePartialSpecialization))
        && (!RD || !TSD || !isTemplateInstance(
            RD->getTemplateSpecializationKind())
         /* RD->getTemplateSpecializationKind()
              < clang::TSK_ImplicitInstantiation */)) {
      registerTemplateDecl(Decl);
      if (RD->getDescribedClassTemplate()
          && (RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)
          && RD->getDescribedClassTemplate()->isThisDeclarationADefinition()) {
        // We are going to visit the content of template records
        if (RD->isThisDeclarationADefinition()) {
          assert((_state & 0x3) <= STempLexicalOut);
          _parents.pushTemplateClass(Decl);
          _state = (State) (_state | STemplateSynchronized);
        };
      }
      else if (RD->isThisDeclarationADefinition()) {
        assert((_state & 0x3) <= STempLexicalOut);
        _parents.pushSemanticLocalClass(Decl);
        _state = (State) (_state | STempLexicalOut);
      }
      // returning false stops the global visit instead of preventing
      //    nested visit.
      return true;
    };
  };
  clang::Decl::Kind declKind = Decl->getDeclContext()->getDeclKind();
  if ((declKind >= clang::Decl::firstFunction
        && declKind <= clang::Decl::lastFunction)) {
    if (static_cast<const clang::FunctionDecl*>(Decl->getDeclContext())
            ->getTemplatedKind() == clang::FunctionDecl::TK_FunctionTemplate) {
      pushTemplateContext();
      assert((_state & 0x3) == SSynchronized);
      _parents.pushTemplateClass(Decl);
      _state = (State) (_state | STemplateSynchronized);
      return true;
    };
  };

  bool isDeportedInstantiation = false;
  // If a struct is used without having been declared (e.g. in a function prototype), then
  // clang inserts a fabricated declaration of the struct just prior to the function declaration.
  // Then if the function has an ACSL comment, the comment attempts to attach to the struct
  // declaration instead of the function prototype, causing a difficult to understand error message.
  // This test is also needed in postSemanticVisitRecordDecl.
  if (!Decl->isEmbeddedInDeclarator()) {
  readRecordComments(Decl, RD, TSD, isDeportedInstantiation);
  }

  tkind templateParameters = NULL;
  const char* name = _clangUtils->get_aggregate_name(Decl, &templateParameters);
  location loc = makeLocation(Decl->getSourceRange());
  ckind type = CCLASS;
  clang::RecordDecl::TagKind tagKind = Decl->getTagKind();
  switch (tagKind) {
    case clang::TTK_Struct:
      type = CSTRUCT;
      break;
    case clang::TTK_Class:
      type = CCLASS;
      break;
    case clang::TTK_Union:
      type = CUNION;
      break;
    default:
      std::cerr << "Unsupported Record Declaration:"
          << name
          << "\nAborting\n";
      exit(2);
  };
  option* body = NULL;
  /* inheritance list */ option inherits = opt_none();
  bool hasEnteredClass = false;
  std::vector<const clang::Decl*> unvisitedInheritance;
  std::vector<const clang::CXXRecordDecl*> unvisitedBases;
  bool isOwnInstance =
    (RD && RD->getKind() == clang::Decl::ClassTemplateSpecialization && TSD
      && isTemplateInstance(RD->getTemplateSpecializationKind()));
  bool isInstance = (isOwnInstance || !_instanceContexts.isEmpty());
  if (RD) {
    clang::CXXRecordDecl* cxxDecl = const_cast<clang::CXXRecordDecl*>(RD);
    if (Decl->isThisDeclarationADefinition() && cxxDecl->isCompleteDefinition())
    { _rttiTable.enterClass(cxxDecl);
      hasEnteredClass = true;
      /* inheritance */ list bodyInherits = makeInheritanceList(cxxDecl,
        isInstance ? &unvisitedInheritance : NULL,
        !isInstance ? &unvisitedBases : NULL);
      free(inherits);
      inherits = opt_some_container(bodyInherits);
    };
  };
  if (declKind == clang::Decl::TranslationUnit
      || declKind == clang::Decl::LinkageSpec
      /* !_parents.hasLexicalContext() */) {
    decl_or_impl_name decl_name = NULL;
    if (Decl->getDeclContext() == Decl->getLexicalDeclContext())
      decl_name = decl_or_impl_name_Declaration(name);
    else {
      qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
      free(const_cast<char*>(qual->decl_name));
      qual->decl_name = name;
      decl_name = decl_or_impl_name_Implementation(qual);
    }
    translation_unit_decl compound =
      translation_unit_decl_Compound(
        loc, decl_name, type, inherits, opt_none(), false,
        templateParameters, Clang_utils::isExternCContext(Decl), _ghost);
    body = &compound->cons_translation_unit_decl.Compound.body;
    if (hasEnteredClass)
      _rttiTable.setVirtualTag(compound->cons_translation_unit_decl.
        Compound.has_virtual);
    if (isOwnInstance) {
      // do not handle partial specialization !
      assert(_instanceContexts.isEmpty());
      pushInstanceContext(_tableForWaitingDeclarations.addInstanceClass(
            RD, compound));
      _state = (State) (_state | SInstanceSynchronized);
      unvisitedDecls().swap(unvisitedInheritance);
      _clangUtils->pushTemplateInstance(TSD->getSpecializedTemplate(),
          &TSD->getTemplateArgs());
      if (!_immediateGlobalDependency.isEmpty()
            && _immediateGlobalDependency.hasGlobalBooked(Decl)) {
        _immediateGlobalDependency.makeTemporaryDependentUnvisited(
          Decl, _tableForWaitingDeclarations);
        _globals.setBeforeBack(
          _immediateGlobalDependency.adjustBeforePlace(Decl));
      }
    }
    else {
      /* translation_unit_decl */ list* place = NULL;
      if (_immediateGlobalDependency.isEmpty()
          || !_immediateGlobalDependency.globalInsertIfBooked(Decl, NULL,
              compound, place, false, *this)) {
        if (hasEnteredClass
            || (Decl->getDeclContext() == Decl->getLexicalDeclContext()))
          _globals.insertContainer(compound);
        else
          _globals.insertBeforeContainer(compound);
        place = _globals.getBeforeBack();
      };
      if (!unvisitedBases.empty()) {
        assert(place);
        std::vector<const clang::CXXRecordDecl*>::const_reverse_iterator
          unvisitedIterEnd = unvisitedBases.rend(), unvisitedIter;
        for (unvisitedIter = unvisitedBases.rbegin();
            unvisitedIter != unvisitedIterEnd; ++unvisitedIter)
          _immediateGlobalDependency.addDeclarationPlace(*unvisitedIter,
              Decl, &_parents.getLexicalParent(), place);
      };
    };
  }
  else {
    if (Decl->getDeclContext()->isRecord() /* _parents.isClass() */) {
      assert(unvisitedBases.empty()
          && (_immediateGlobalDependency.isEmpty()
            || !_immediateGlobalDependency.hasGlobalBooked(Decl)));
      // get rid of a spurious nested declaration of the record
      if (Decl->isThisDeclarationADefinition()
          || Decl->getName() != ((const clang::RecordDecl*)
              Decl->getDeclContext())->getName()) {
        if (isOwnInstance) {
          // do not handle partial specialization !
          if (_instanceContexts.isEmpty()) {
            qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
            free(const_cast<char*>(qual->decl_name));
            qual->decl_name = name;
            decl_or_impl_name decl_name
                = decl_or_impl_name_Implementation(qual);
            translation_unit_decl compound =
              translation_unit_decl_Compound(
                loc, decl_name, type, inherits, opt_none(), false,
                templateParameters, false, _ghost);
            body = &compound->cons_translation_unit_decl.Compound.body;
            pushInstanceContext(_tableForWaitingDeclarations.addInstanceClass(
                RD, compound));
            _state = (State) (_state | SInstanceSynchronized);
            unvisitedDecls().swap(unvisitedInheritance);
            _clangUtils->pushTemplateInstance(TSD->getSpecializedTemplate(),
                &TSD->getTemplateArgs());
            if (hasEnteredClass)
              _rttiTable.setVirtualTag(compound->cons_translation_unit_decl.
                Compound.has_virtual);
          }
          else {
            assert(_parents.hasLexicalContext() && _parents.isClass());
            class_decl compound
              = class_decl_CCompound(loc, name, type, inherits, opt_none(),
                  templateParameters, false);
            class_decl compound_decl = class_decl_CCompound(copy_loc(loc),
              strdup(name), type, opt_none(), opt_none(),
              tkind_dup(templateParameters), false);
            _parents.add(compound_decl);
            body = &compound->cons_class_decl.CCompound.body;
            pushInstanceContext(_tableForWaitingDeclarations.addSubClass(
              _instanceContexts.firstClassContext(),
              _instanceContexts.lastSubClassContext(), RD, compound));
            _state = (State) (_state | SInstanceSynchronized);
            unvisitedDecls().swap(unvisitedInheritance);
            _clangUtils->pushTemplateInstance(TSD->getSpecializedTemplate(),
                &TSD->getTemplateArgs());
            if (hasEnteredClass)
              _rttiTable.setVirtualTag(compound->cons_class_decl.
                CCompound.has_virtual);
          };
        }
        else if (!_instanceContexts.isEmpty()) {
          assert(_parents.hasLexicalContext() && _parents.isClass());
          class_decl compound
            = class_decl_CCompound(loc, name, type, inherits, opt_none(),
                templateParameters, false);
          class_decl compound_decl = class_decl_CCompound(copy_loc(loc),
            strdup(name), type, opt_none(), opt_none(),
            tkind_dup(templateParameters), false);
          _parents.add(compound_decl);
          body = &compound->cons_class_decl.CCompound.body;
          pushInstanceContext(_tableForWaitingDeclarations.addSubClass(
            _instanceContexts.firstClassContext(),
            _instanceContexts.lastSubClassContext(), RD, compound));
          _state = (State) (_state | SInstanceSynchronized);
          unvisitedDecls().swap(unvisitedInheritance);
          if (TSD)
            _clangUtils->pushTemplateInstance(TSD->getSpecializedTemplate(),
                &TSD->getTemplateArgs());
          if (hasEnteredClass)
            _rttiTable.setVirtualTag(compound->cons_class_decl.
              CCompound.has_virtual);
        }
        else if (_parents.hasLexicalContext() && _parents.isClass()) {
          assert(unvisitedBases.empty());
          class_decl compound
            = class_decl_CCompound(loc, name, type, inherits, opt_none(),
                templateParameters, false);
          body = &compound->cons_class_decl.CCompound.body;
          _parents.add(compound);
          if (hasEnteredClass)
            _rttiTable.setVirtualTag(compound->cons_class_decl.
              CCompound.has_virtual);
        }
        else {
          qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
          free(const_cast<char*>(qual->decl_name));
          qual->decl_name = name;
          decl_or_impl_name decl_name = decl_or_impl_name_Implementation(qual);
          translation_unit_decl compound = translation_unit_decl_Compound(
             loc, decl_name, type, inherits, opt_none(), false,
             templateParameters, false, _ghost);
          body = &compound->cons_translation_unit_decl.Compound.body;
          if (hasEnteredClass)
            _rttiTable.setVirtualTag(compound->cons_translation_unit_decl.
              Compound.has_virtual);
          if (_parents.hasLexicalContext())
            _parents.add(compound);
          else
            _globals.insertContainer(compound);
        };
      }
      else {
        free(loc);
        if (inherits->is_some) {
          /* inheritance */ list bodyInherits
              = (list) inherits->content.container;
          while (bodyInherits) {
            list tmp = bodyInherits->next;
            free_inheritance((inheritance) bodyInherits->element.container);
            free(bodyInherits);
            bodyInherits = tmp;
          };
        }
        if (templateParameters)
          free_tkind(templateParameters);
        free(inherits);
        free(const_cast<char*>(name));
        return true;
      };
    }
    else if (declKind == clang::Decl::Function) {
      // ex: _GLIBCXX_RESOLVE_LIB_DEFECTS
      // 167.  Improper use of traits_type::length()
      assert(Decl->getDeclContext() == Decl->getLexicalDeclContext());
      qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
      free(const_cast<char*>(qual->decl_name));
      qual->decl_name = name;
      decl_or_impl_name decl_name = NULL;
      decl_name = decl_or_impl_name_Implementation(qual);
      translation_unit_decl compound =
        translation_unit_decl_Compound(
          loc, decl_name, type, inherits,
          opt_none(), false, templateParameters, false,_ghost);
      body = &compound->cons_translation_unit_decl.Compound.body;
      if (hasEnteredClass)
        _rttiTable.setVirtualTag(compound->cons_translation_unit_decl.
          Compound.has_virtual);
      _globals.insertContainer(compound);
    }
    else {
      assert(Decl->getDeclContext()->isNamespace() /*_parents.isNamespace() */);
      decl_or_impl_name decl_name = NULL;
      if (Decl->getDeclContext() == Decl->getLexicalDeclContext()
          && !(RD && RD->getKind() == clang::Decl::ClassTemplateSpecialization
            && TSD))
        decl_name = decl_or_impl_name_Declaration(name);
      else {
        qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
        free(const_cast<char*>(qual->decl_name));
        qual->decl_name = name;
        decl_name = decl_or_impl_name_Implementation(qual);
      };
      translation_unit_decl compound =
        translation_unit_decl_Compound(
          loc, decl_name, type, inherits,
          opt_none(), false, templateParameters, false,_ghost);
      body = &compound->cons_translation_unit_decl.Compound.body;
      if (hasEnteredClass)
        _rttiTable.setVirtualTag(compound->cons_translation_unit_decl.
          Compound.has_virtual);
      if (isOwnInstance) {
        // do not handle partial specialization !
        // const clang::ClassTemplateSpecializationDecl* TSD
        //    = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(RD);

        // assert(_instanceContexts.isEmpty());
        // could be technically inside an instance class since instantiation
        // points may be a friend class inside another class
        if (!_instanceContexts.isEmpty()) {
          // push _instanceContext to manage the instances of friend classes
          // inside our class.
          _alternateInstanceContexts.push_back(std::make_pair(Decl,
              FramaCIRGenAction::InstanceContexts()));
          _alternateInstanceContexts.back().second.swap(_instanceContexts);
        }
        pushInstanceContext(_tableForWaitingDeclarations.addInstanceClass(
              RD, compound));
        _state = (State) (_state | SInstanceSynchronized);
        unvisitedDecls().swap(unvisitedInheritance);
        _clangUtils->pushTemplateInstance(TSD->getSpecializedTemplate(),
            &TSD->getTemplateArgs());
        if (!_immediateGlobalDependency.isEmpty()
              && _immediateGlobalDependency.hasGlobalBooked(Decl))
          _immediateGlobalDependency.makeTemporaryDependentUnvisited(
            Decl, _tableForWaitingDeclarations);
      }
      else {
        /* translation_unit_decl */ list* place = NULL;
        if (_immediateGlobalDependency.isEmpty()
            || !_immediateGlobalDependency.globalInsertIfBooked(Decl,
                &_parents.getLexicalParent(), compound, place, false, *this)) {
          if (_parents.hasLexicalContext()) {
            // work around desynchronization between clang and our own
            // context. Apparently only manifests for template instances
            // that do not declare anything (hence are useless): just drop
            // them.
            // TODO: get rid of our own LocalContext and rely solely on
            // Clang's.
            if (_parents.isNamespace()) _parents.add(compound, &place);
          else {
            _globals.insertContainer(compound);
            place = _globals.getBeforeBack();
          };
        };
        };
        if (!unvisitedBases.empty()) {
          assert(place);
          std::vector<const clang::CXXRecordDecl*>::const_reverse_iterator
            unvisitedIterEnd = unvisitedBases.rend(), unvisitedIter;
          for (unvisitedIter = unvisitedBases.rbegin();
              unvisitedIter != unvisitedIterEnd; ++unvisitedIter)
            _immediateGlobalDependency.addDeclarationPlace(*unvisitedIter,
                Decl, &_parents.getLexicalParent(), place);
        };
      };
    };
  };

  assert(_state == SSynchronized || _state == SInstanceSynchronized);
  _parents.pushClass(*body, Decl);
  return true;
}

bool FramacVisitor::VisitClassTemplatePartialSpecializationDecl(
  clang::CXXRecordDecl* Decl) {
  if (!_ghost && isGhostDecl(Decl)) return true;
  if (/* _parents. */ hasTemplateContext() && _parents.isSemanticLocalClass())
    handleSemanticPostVisit(Decl->getParent());
  else
    handlePostVisit(Decl->getLexicalDeclContext(), Decl->getParent());
  if (!hasTemplateContext() || !_parents.isSemanticLocalClass())
    _lexicalContextForPostVisit = Decl;
  _semanticContextForPostVisit = Decl;
  if (Decl->isThisDeclarationADefinition())
    pushTemplateContext();

  registerAttachedNextTemplateDecl(Decl);
  if (Decl->isThisDeclarationADefinition()) {
    // We are going to visit the content of template records
    if (/* _parents. */ hasTemplateContext() && _parents.isSemanticLocalClass())
    { assert((_state & 0x3) == STempLexicalOut);
      _parents.pushSemanticLocalTemplateClass(Decl);
    }
    else {
      assert((_state & 0x3) == SSynchronized);
      _parents.pushTemplateClass(Decl);
    };
    _state = (State) (_state | STemplateSynchronized);
  };

  // returning false stops the global visit instead of preventing
  //    nested visit.
  return true;
}

void FramacVisitor::postLexicalVisitRecordDecl(clang::RecordDecl* Decl,
    int& templateContextsNumber) {
  const clang::CXXRecordDecl *RD = llvm::dyn_cast<clang::CXXRecordDecl>(Decl);
  const clang::ClassTemplateSpecializationDecl* TSD = NULL;
  if (Decl->getKind() == clang::Decl::ClassTemplateSpecialization)
    TSD = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(Decl);
  if ((templateContextsNumber > 0
        || (RD && RD->getDescribedClassTemplate()
          && RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)
        || ( RD->getKind() == clang::Decl::ClassTemplatePartialSpecialization))
      && (!RD || !TSD || !isTemplateInstance(
          RD->getTemplateSpecializationKind()))) {
    if (Decl->isThisDeclarationADefinition()) {
      const clang::DeclContext* parentDecl = Decl->getLexicalDeclContext();
      clang::Decl::Kind declKind = parentDecl->getDeclKind();
      if ((declKind >= clang::Decl::firstFunction
            && declKind <= clang::Decl::lastFunction))
         parentDecl = parentDecl->getLexicalParent();
      // the case STemp.. occurs because postSemanticVisitRecordDecl
      //   has not still been called.
      // assert(_state == STemplateSynchronized);
      assert(templateContextsNumber > 0);
      if (RD &&
          ((RD->getDescribedClassTemplate()
            && (RD->getDescribedClassTemplate()->getTemplatedDecl() == RD))
          || (RD->getKind()==clang::Decl::ClassTemplatePartialSpecialization)))
        --templateContextsNumber;
      _parents.lexicalSynchronizeWith(parentDecl, *this);
      if (templateContextsNumber == 0)
         _state = hasInstanceContext() ? SInstanceSynchronized : SSynchronized;
      else
         _state = STemplateSynchronized;
    };
    return;
  };

  bool hasInsertedGlobals = false;
  if (RD && RD->getKind() == clang::Decl::ClassTemplateSpecialization && TSD
      && isTemplateInstance(RD->getTemplateSpecializationKind())) {
    if (_parents.getLexicalParent().back().isLocalClass())
      goto LSynchronization;
    // do not handle partial specialization!
    bool hasAlternate = false;
    if (_instanceContexts.size() == 1) {
      VisitTable::MissingClassGeneration* lastInstance
          = &_instanceContexts.lastClassContext();
      assert(lastInstance->isInstanceClass());
      translation_unit_decl* last = _globals.getBack()
        ? (translation_unit_decl*) &_globals.getBack()->element.container
        : NULL;
      list* beforeBack = _globals.getBack()
        ? &_globals.getBack()->next : &_globals.getFront();
      list oldBack = _globals.getBack();
      translation_unit_decl originalCompound = ((VisitTable
        ::InstanceClassGeneration*) lastInstance)->getWaitingClassDeclaration();
      _tableForWaitingDeclarations.setInstanceClassAsComplete(
          (VisitTable::InstanceClassGeneration*) lastInstance, _globals);
      if (_globals.getBack() && last !=
          (translation_unit_decl*) &_globals.getBack()->element.container) {
        if (!_immediateGlobalDependency.isEmpty()
            && _immediateGlobalDependency.hasGlobalBooked(Decl)) {
          assert(*beforeBack);
          translation_unit_decl compound
            = (translation_unit_decl) (*beforeBack)->element.container;
          list compoundPlace = *beforeBack;
          *beforeBack = (*beforeBack)->next; // temporary remove compound
          // remove compound original with a consistent _globals
          if (_globals.getBack() == compoundPlace)
            _globals.resetBack(oldBack ? oldBack : _globals.getFront());
          free(compoundPlace);
          _immediateGlobalDependency.makeTemporaryDependentVisited(
              Decl, _tableForWaitingDeclarations, _globals);
          /* translation_unit_decl */ list* place = NULL;
          _immediateGlobalDependency.globalInsertIfBooked(Decl,
              &_parents.getLexicalParent(), compound, place, true, *this);
          _globals.setBeforeBack(place);
        }
        else
          _globals.setBeforeBack(beforeBack);
        hasInsertedGlobals = true;
      }
      else { // insert at least the declaration
        assert(originalCompound->tag_translation_unit_decl == COMPOUND);
        _globals.insertContainer(translation_unit_decl_Compound(
          copy_loc(originalCompound->cons_translation_unit_decl.Compound.loc),
          decl_or_impl_name_dup(originalCompound->cons_translation_unit_decl
            .Compound.name),
          originalCompound->cons_translation_unit_decl.Compound.kind,
          opt_none() /* inherits */, opt_none() /* body */,
          false /* has_virtual */,
          tkind_dup(originalCompound->cons_translation_unit_decl
            .Compound.template_kind), false /* is_extern_c_context */,
          false /* is_ghost */));
        _globals.setBeforeBack(beforeBack);
        hasInsertedGlobals = true;
      }
      // are we in an instance of a friend class inside another class?
      hasAlternate = !_alternateInstanceContexts.empty()
          && _alternateInstanceContexts.back().first == Decl;
      assert(!hasAlternate
          || !_alternateInstanceContexts.back().second.isEmpty());
    }
    else {
      /* class_decl */ list* parentBody = NULL;
      VisitTable::MissingSubClassGeneration* lastInstance
          = _instanceContexts.lastSubClassContext(&parentBody);
      assert(lastInstance && parentBody);
      class_decl originalCompound = lastInstance->getWaitingSubClassDecl();
      ForwardReferenceList* body = _parents.getDeclList(parentBody);
      ForwardReferenceList additionalBody;
      if (!body)
        additionalBody = ForwardReferenceList(*parentBody);
      if (!lastInstance->setAsComplete(body ? *body : additionalBody)) {
        assert(originalCompound->tag_class_decl == CCOMPOUND);
        (body ? *body : additionalBody).insertContainer(class_decl_CCompound(
          copy_loc(originalCompound->cons_class_decl.CCompound.loc),
          strdup(originalCompound->cons_class_decl.CCompound.name),
          originalCompound->cons_class_decl.CCompound.kind,
          opt_none() /* inherits */, opt_none() /* body */,
          tkind_dup(originalCompound->cons_class_decl.CCompound.template_kind),
          false /* has_virtual */));
      };
      _tableForWaitingDeclarations.addSubDeclaration(Decl, 
          _instanceContexts.getRootDecl(),
          lastInstance /* should be the stack of subclasses */,
          _globals);
    };
    assert(_state >= SInstanceSynchronized);
    popInstanceContext(RD);
    if (hasAlternate) {
      // we are in an instance of a friend class inside another class.
      // so we restore the initial class context.
      _instanceContexts.swap(_alternateInstanceContexts.back().second);
      _alternateInstanceContexts.pop_back();
    };
    if (!hasInstanceContext())
      _state = (State) (_state & 0x3);
    if (_templateCommentIndex >= -1)
      _templateCommentIndex = -2;
  }
  else {
    bool hasVisited = false;
    if (Decl->getDeclContext()->isRecord() /* _parents.isClass() */) {
      // get rid of a spurious nested declaration of the record
      if (Decl->isThisDeclarationADefinition()
          || Decl->getName() != ((const clang::RecordDecl*)
              Decl->getDeclContext()/* _parents.getSynchro() */)->getName()) {
        if (_instanceContexts.size() > 1) {
          /* class_decl */ list* parentBody = NULL;
          VisitTable::MissingSubClassGeneration* lastInstance
              = _instanceContexts.lastSubClassContext(&parentBody);
          assert(lastInstance && parentBody);
          class_decl originalCompound = lastInstance->getWaitingSubClassDecl();
          ForwardReferenceList* body = _parents.getDeclList(parentBody);
          ForwardReferenceList additionalBody;
          if (!body)
            additionalBody = ForwardReferenceList(*parentBody);
          if (!lastInstance->setAsComplete(body ? *body : additionalBody)) {
            assert(originalCompound->tag_class_decl == CCOMPOUND);
            (body ? *body : additionalBody).insertContainer(class_decl_CCompound(
              copy_loc(originalCompound->cons_class_decl.CCompound.loc),
              strdup(originalCompound->cons_class_decl.CCompound.name),
              originalCompound->cons_class_decl.CCompound.kind,
              opt_none() /* inherits */, opt_none() /* body */,
              tkind_dup(originalCompound->cons_class_decl.CCompound.template_kind),
              false /* has_virtual */));
          };
          assert(_state >= SInstanceSynchronized);
          popInstanceContext(RD);
          if (!hasInstanceContext())
            _state = (State) (_state & 0x3);
          _tableForWaitingDeclarations.addSubDeclaration(Decl, 
              _instanceContexts.getRootDecl(),
              lastInstance /* should be the stack of subclasses */,
              _globals);
          hasVisited = true;
        };
      };
    };
    if (!hasVisited)
      _tableForWaitingDeclarations.addDeclaration(Decl, _globals);
    // _instanceContexts.removeUnvisited(Decl);
  };

  if (!_parents.hasLexicalLocalContext(Decl)) {
    if (llvm::isa<clang::CXXRecordDecl>(Decl)) {
      clang::CXXRecordDecl* cxxDecl = static_cast<clang::CXXRecordDecl*>(Decl);
      if (cxxDecl->isCompleteDefinition()) {
        location loc = makeLocation(Decl->getSourceRange());
        assert(_parents.isClass());
        _rttiTable.exitClass(*_clangUtils, _parents.getClassContent(), _globals,
          loc);
        free_location(loc);
      };
    };
  }
  else { /* assert(false); */ }

LSynchronization:
  const clang::DeclContext* parentDecl = Decl->getLexicalDeclContext();
  clang::Decl::Kind declKind = parentDecl->getDeclKind();
  if ((declKind >= clang::Decl::firstFunction
        && declKind <= clang::Decl::lastFunction))
    parentDecl = parentDecl->getLexicalParent();
  _parents.lexicalSynchronizeWith(parentDecl, *this);
  if (!hasTemplateContext())
    _state = hasInstanceContext() ? SInstanceSynchronized : SSynchronized;
  else
    _state = STemplateSynchronized;

  if (hasInsertedGlobals && _parents.isNamespace())
    _parents.reopenLexicalHierarchy(*this);
}

void FramacVisitor::postSemanticVisitRecordDecl(clang::RecordDecl* Decl) {
  const clang::CXXRecordDecl *RD = llvm::dyn_cast<clang::CXXRecordDecl>(Decl);
  const clang::ClassTemplateSpecializationDecl* TSD = NULL;
  if (Decl->getKind() == clang::Decl::ClassTemplateSpecialization)
    // do not handle partial specialization !
    TSD = llvm::dyn_cast<clang::ClassTemplateSpecializationDecl>(Decl);
  if ((/* _parents. */ hasTemplateContext()
        || (RD && RD->getDescribedClassTemplate()
          && RD->getDescribedClassTemplate()->getTemplatedDecl() == RD)
        || ( RD->getKind() == clang::Decl::ClassTemplatePartialSpecialization))
      && (!RD || !TSD || !isTemplateInstance(
          RD->getTemplateSpecializationKind()))) {
    registerTemplateDecl(Decl);
    const clang::DeclContext* parentDecl = Decl->getParent();
    clang::Decl::Kind declKind = parentDecl->getDeclKind();
    if ((declKind >= clang::Decl::firstFunction
          && declKind <= clang::Decl::lastFunction))
      parentDecl = parentDecl->getParent();
    if (RD->isThisDeclarationADefinition()) {
      // note that the semantic parent Stack may be greater than one.
      assert(_state==STemplateSynchronized||_state==STemplateTempLexicalOut);
      _parents.semanticSynchronizeWith(parentDecl, *this);
      if (!hasTemplateContext()) {
        if (_state == STemplateSynchronized) {
          assert(!_parents.isSemanticLocalClass());
          _state = hasInstanceContext() ? SInstanceSynchronized : SSynchronized;
        }
        else if (_parents.isSemanticLocalClass())
          _state = hasInstanceContext() ? SInstanceTempLexicalOut
             : STempLexicalOut;
        else
          _state = hasInstanceContext() ? SInstanceSynchronized : SSynchronized;
      }
    }
    else {
      // assert(_parents.getSemanticParentContext() == parentDecl);
      if (_parents.getSemanticParentContext() != parentDecl) {
        _parents.semanticSynchronizeWith(parentDecl, *this);
        if (!hasTemplateContext()) {
          if (_state == STemplateSynchronized) {
            assert(!_parents.isSemanticLocalClass());
            _state=hasInstanceContext() ? SInstanceSynchronized : SSynchronized;
          }
          else if (_parents.isSemanticLocalClass())
            _state = hasInstanceContext() ? SInstanceTempLexicalOut
               : STempLexicalOut;
          else
            _state=hasInstanceContext() ? SInstanceSynchronized : SSynchronized;
        }
        if (llvm::dyn_cast<const clang::NamespaceDecl>(parentDecl)) {
        const clang::NamespaceDecl* fst = llvm::dyn_cast
            <const clang::NamespaceDecl>(_parents.getSemanticParentContext()),
          *snd = llvm::dyn_cast<const clang::NamespaceDecl>(parentDecl);
        assert(fst && snd && fst->getName() == snd->getName());
      };
    };
    };
    if (_templateCommentIndex >= -1)
      _templateCommentIndex = -2;
    return;
  };

  // See the comment in VisitRecordDecl about the isEmbeddedInDeclarator check
  if (!_parents.hasSemanticLocalContext(Decl)&& !Decl->isEmbeddedInDeclarator()) {
    readInnerRecordComments(Decl);
  }

  bool isOwnInstance = RD
    && RD->getKind() == clang::Decl::ClassTemplateSpecialization && TSD
    && isTemplateInstance(RD->getTemplateSpecializationKind());
  // should be done by postLexicalVisitRecordDecl.
  if (isOwnInstance) {
    // do not handle partial specialization!
    _clangUtils->popTemplateInstance(TSD->getSpecializedTemplate());
    if (_templateCommentIndex >= -1)
      _templateCommentIndex = -2;
  }
  else if (Decl->getDeclContext()->isRecord() /* _parents.isClass() */
      && (Decl->isThisDeclarationADefinition()
          || Decl->getName() != ((const clang::RecordDecl*)
              Decl->getDeclContext())->getName())
      && !_instanceContexts.isEmpty() && TSD)
    // this condition is a special case of VisitRecordDecl
    //   to get the symmetric case of _clangUtils->pushTemplateInstance
    _clangUtils->popTemplateInstance(TSD->getSpecializedTemplate());

  const clang::DeclContext* parentDecl = Decl->getParent();
  clang::Decl::Kind declKind = parentDecl->getDeclKind();
  if ((declKind >= clang::Decl::firstFunction
        && declKind <= clang::Decl::lastFunction))
    parentDecl = parentDecl->getParent();
  _parents.semanticSynchronizeWith(parentDecl, *this);
  if (!hasTemplateContext()) {
    if (_state == STemplateSynchronized) {
      assert(!_parents.isSemanticLocalClass());
      _state = hasInstanceContext() ? SInstanceSynchronized : SSynchronized;
    }
    else if (_parents.isSemanticLocalClass())
      _state = hasInstanceContext() ? SInstanceTempLexicalOut
         : STempLexicalOut;
    else
      _state = hasInstanceContext() ? SInstanceSynchronized : SSynchronized;
  }
  else {
    if (_state == STemplateSynchronized)
      assert(!_parents.isSemanticLocalClass());
    else if (_parents.isSemanticLocalClass())
      _state = STemplateTempLexicalOut;
    else
      _state = STemplateSynchronized;
  }
}

bool FramacVisitor::VisitTypedefNameDecl(clang::TypedefNameDecl* Decl) {
  if (!_ghost && isGhostDecl(Decl)) return true;
  { clang::Decl::Kind declKind = Decl->getDeclContext()->getDeclKind();
    if (declKind >= clang::Decl::firstFunction
          && declKind <= clang::Decl::lastFunction) {
      if (static_cast<const clang::FunctionDecl*>(Decl->getDeclContext())
          ->getTemplatedKind() != clang::FunctionDecl::TK_FunctionTemplate)
        _tableForWaitingDeclarations.addDeclaration(Decl, _globals);
      return true;
    };
  }
  if (/* _parents. */ hasTemplateContext() && _parents.isSemanticLocalClass())
    handleSemanticPostVisit(Decl->getDeclContext());
  else
    handlePostVisit(Decl->getLexicalDeclContext(), Decl->getDeclContext());
  if (/* _parents. */ hasTemplateContext()
      // type alias is basically a templated typedef
      || Decl->getKind() == clang::Decl::TypeAlias) {
    registerTemplateDecl(Decl);
    // because sometimes instance declarations depends on template typedef.
    _tableForWaitingDeclarations.addDeclaration(Decl, _globals);
    return true;
  };
  if (Decl->getSourceRange().getBegin().isValid())
    readGlobalComment(Decl, true /* mayHaveTemplate */);

  if (_generatedTypedefsInAdvance.find(Decl)
      == _generatedTypedefsInAdvance.end()) {
    const char* name;
    if (!_parents.hasLexicalContext())
      name = copy_string(Decl->getQualifiedNameAsString());
    else
      name = copy_string(Decl->getName().str());
    location loc = makeLocation(Decl->getSourceRange());
    qual_type targetType=
      makeDefaultNameType(Decl->getLocation(), Decl->getUnderlyingType());
    if (!_parents.hasLexicalContext()) {
      translation_unit_decl decl =
        translation_unit_decl_Typedef(
          loc, decl_or_impl_name_Declaration(name), targetType,
          Clang_utils::isExternCContext(Decl->getDeclContext()),_ghost);
      _globals.insertContainer(decl);
    }
    else {
      if (_parents.isClass()) {
        class_decl decl = class_decl_CTypedef(loc, name, targetType);
        _parents.add(decl);
      }
      else {
        assert(_parents.isNamespace());
        translation_unit_decl decl =
          translation_unit_decl_Typedef(
            loc, decl_or_impl_name_Declaration(name), targetType,
            Clang_utils::isExternCContext(Decl->getDeclContext()), _ghost);
        _parents.add(decl);
      };
    };
  };
  _tableForWaitingDeclarations.addDeclaration(Decl, _globals);
  return true;
}

bool FramacVisitor::VisitVarDecl(clang::VarDecl* Decl) {
  if (!_ghost && isGhostDecl(Decl)) return true;
  { clang::Decl::Kind declKind = Decl->getDeclContext()->getDeclKind();
    if ((declKind >= clang::Decl::firstFunction
          && declKind <= clang::Decl::lastFunction)
        && (static_cast<const clang::FunctionDecl*>(Decl->getDeclContext())
            ->getTemplatedKind() == clang::FunctionDecl::TK_FunctionTemplate))
      return true;
  }
  // static local variables get visited as well
  if (Decl->getDeclContext()->isFunctionOrMethod()) return true;
  if (Decl->hasGlobalStorage()) {
    if (/* _parents. */ hasTemplateContext() && _parents.isSemanticLocalClass())
      handleSemanticPostVisit(Decl->getDeclContext());
    else
      handlePostVisit(Decl->getLexicalDeclContext(), Decl->getDeclContext());
  };
  if (/* _parents. */ hasTemplateContext()) {
    registerTemplateDecl(Decl);
    return true;
  };

  if (!Decl->hasGlobalStorage())
    return true;
  readGlobalComment(Decl, true /* mayHaveTemplate */);

  const char* name = _clangUtils->get_field_name(Decl);
  location loc = makeLocation(Decl->getSourceRange());
  clang::QualType type = Decl->getType();
  ickind constantType = ICLITERAL;
  int64_t value = 0;
  if (type.isConstQualified()
      && (type->getTypeClass() == clang::Type::Builtin)) {
    auto builtinType =
      llvm::dyn_cast<const clang::BuiltinType>(type.getTypePtr());
    assert(builtinType);
    if (builtinType->isInteger()) {
      clang::EvaluatedStmt *Eval = Decl->ensureEvaluatedStmt();
      if (Eval->WasEvaluated || Eval->Value) {
        clang::APValue* resultingValue = Decl->evaluateValue();
        if (resultingValue) {
          constantType = Decl->hasExternalStorage()?ICEXTERNCONST:ICSTATICCONST;
          clang::APValue* resultingValue = Decl->evaluateValue();
          value=(int64_t) resultingValue->getInt().getLimitedValue(UINT64_MAX);
        }
      };
    };
  };
  qual_type declarationType = makeDefaultType(Decl->getLocation(), type);
  if (Decl->getCanonicalDecl()->getStorageClass() == clang::SC_Static &&
      !Decl->isOutOfLine())
    declarationType->qualifier = cons_plain(STATIC, declarationType->qualifier);
  option /*init_expr*/ init = opt_none();
  if (Decl->getInit()) {
    variable v = variable_Global(_clangUtils->makeQualifiedName(*Decl));
    const clang::Type* typ = Decl->getType().getTypePtr();
    if (isRecordOrRecordRef(typ) || typ->isConstantArrayType()) {
      location loc = makeLocation(Decl->getSourceRange());
      _implicitThisStar = expression_cons(loc,exp_node_Variable(v));
    }
    free(init);
    init = opt_some_container(makeInitExpr(Decl->getType(), Decl->getInit()));
    if (!_cleanups.empty()) {
      std::cerr << "Unsupported statements to clean the expression\n";
#if CLANG_VERSION_MAJOR >= 11
      Decl->getInit()->dump(llvm::errs(), *_context);
#else
      Decl->getInit()->dump(llvm::errs(), _context->getSourceManager());
#endif
      std::cerr << "\ncontinue the translation\n";
      _cleanups.clear();
    };
  };

  clang::Decl::Kind declKind = Decl->getDeclContext()->getDeclKind();
  if (declKind == clang::Decl::TranslationUnit
      || declKind == clang::Decl::LinkageSpec
      /* !_parents.hasLexicalContext() */) {
    translation_unit_decl decl = NULL;
    if (constantType == ICLITERAL) {
      decl_or_impl_name decl_name = NULL;
      if (Decl->getDeclContext() == Decl->getLexicalDeclContext())
        decl_name = decl_or_impl_name_Declaration(name);
      else {
        qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
        free(const_cast<char*>(qual->decl_name));
        qual->decl_name = name;
        decl_name = decl_or_impl_name_Implementation(qual);
      };
      decl =
        translation_unit_decl_GlobalVarDecl(
          loc, decl_name, declarationType, init,
          Decl->isInExternCContext(), _ghost);
    }
    else {
      ikind kind = _clangUtils->makeIntConstantType(type.getTypePtr());
      // Apparently isExternC() is not strong enough for this kind of 
      // identifiers
      decl =
        translation_unit_decl_StaticConst(
          loc, name, kind, constantType, value,
          Decl->isInExternCContext(), _ghost);
    };
    _globals.insertContainer(decl);
  }
  else {
    if (Decl->getDeclContext()->isRecord() /* _parents.isClass() */) {
      if (constantType == ICLITERAL) {
        if (_parents.hasLexicalContext() && _parents.isClass()) {
          class_decl decl =
            class_decl_CFieldDecl(
              loc, name, declarationType, opt_none(), false);
          _parents.add(decl);
        }
        else {
          qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
          free(const_cast<char*>(qual->decl_name));
          qual->decl_name = name;
          decl_or_impl_name decl_name = decl_or_impl_name_Implementation(qual);
          translation_unit_decl decl =
            translation_unit_decl_GlobalVarDecl(
              loc, decl_name, declarationType, init, false, _ghost);
          if (_parents.hasLexicalContext()) {
            _parents.add(decl);
          } else {
            _globals.insertContainer(decl);
          };
        };
      }
      else {
        assert(_parents.isClass());
        ikind kind = _clangUtils->makeIntConstantType(type.getTypePtr());
        class_decl decl = class_decl_CStaticConst(loc, name, kind,
            constantType, value);
        _parents.add(decl);
      };
    }
    else {
      translation_unit_decl decl = NULL;
      if (constantType== ICLITERAL) {
        decl_or_impl_name decl_name = NULL;
        if (!Decl->getDeclContext()->isNamespace()
            || (Decl->getDeclContext() == Decl->getLexicalDeclContext()))
          decl_name = decl_or_impl_name_Declaration(name);
        else {
          qualified_name qual = _clangUtils->makeQualifiedName(*Decl);
          free(const_cast<char*>(qual->decl_name));
          qual->decl_name = name;
          decl_name = decl_or_impl_name_Implementation(qual);
        }
        decl =
          translation_unit_decl_GlobalVarDecl(
            loc, decl_name, declarationType, init, false, _ghost);
      }
      else {
        ikind kind = _clangUtils->makeIntConstantType(type.getTypePtr());
        decl =
          translation_unit_decl_StaticConst(
            loc, name, kind, constantType, value, false, _ghost);
      };
      if (_parents.hasLexicalContext())
        _parents.add(decl);
      else {
        _globals.insertContainer(decl);
      };    
    };
  };
  _tableForWaitingDeclarations.addDeclaration(Decl, _globals);
  _instanceContexts.removeUnvisited(Decl);
  return true;
}

bool FramacVisitor::VisitFieldDecl(clang::FieldDecl* Decl) {
  if (!_ghost && isGhostDecl(Decl)) return true;
  if (/* _parents. */ hasTemplateContext()) {
    if (_parents.isSemanticLocalClass())
      handleSemanticPostVisit(Decl->getDeclContext());
    else
      handlePostVisit(Decl->getLexicalDeclContext(), Decl->getDeclContext());
    registerTemplateDecl(Decl);
    return true;
  };
  handlePostVisit(Decl->getLexicalDeclContext(), Decl->getDeclContext());
  assert(_parents.hasLexicalContext() && _parents.isClass());
  readGlobalComment(Decl, true /* mayHaveTemplate */);

  const char* name = _clangUtils->get_field_name(Decl);
  clang::SourceLocation sloc = Decl->getLocation(); 
  location loc = makeLocation(Decl->getSourceRange());
  /* Decl may be a bitfield */
  clang::QualType type = Decl->getType();
  qual_type declarationType;
  if (!Clang_utils::isExternCContext(Decl->getDeclContext()))
    declarationType = makeDefaultType(sloc, type);
  else
    declarationType = _clangUtils->makePODType(sloc, type);

  class_decl decl;
  if (!Decl->isBitField())
    decl =
      class_decl_CFieldDecl(
        loc, name, declarationType, opt_none(), Decl->isMutable());
  else {
    int size = Decl->getBitWidthValue(*_context);
    decl =
      class_decl_CFieldDecl(
        loc, name, declarationType, opt_some_plain(size), Decl->isMutable());
  };
  _parents.add(decl);
  _tableForWaitingDeclarations.addDeclaration(Decl, _globals);
  _instanceContexts.removeUnvisited(Decl);
  return true;
}

void FramacVisitor::postHandleTranslationUnit() {
  _parents.clear(*this);
  int previousComment = _commentIndex;
  _commentIndex = (int) _annotationCommentList.size()-2;
  while (previousComment <= _commentIndex) {
    ++previousComment;
    switch (_annotationCommentList[previousComment]->getKind()) {
      case AnnotationComment::KGlobal:
        parseGlobalComment(*_annotationCommentList[previousComment],
            _context->getTranslationUnitDecl());
        break;
      case AnnotationComment::KGhost:
          parseGhostGlobal(*_annotationCommentList[previousComment],
                           _context->getTranslationUnitDecl());
          break;
      default:
        parseDefaultComment(*_annotationCommentList[previousComment]);
        break;
    };
  };
}

