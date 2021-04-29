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

// -*- C++ -*-
/* Functions for manipulating Clang structures and
   transforming them into intermediate AST, that are shared between main AST
   and ACSL
 */

#ifndef Clang_utilsH
#define Clang_utilsH

#include <iostream>
#include <sstream>
#include <cstddef>
#include <list>
#include <set>
#include <map>
#include <functional>
#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif
#include "clang/Basic/Version.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/FileManager.h"
#if defined(__GNUC__) && !defined(__clang__)
#pragma GCC diagnostic pop
#endif

extern "C" {
#include "intermediate_format.h"

void free_type(qual_type obj);

}

static inline const char*
copy_string(const std::string& s) {
   return (s.length() > 0) ? strdup(s.c_str()) : strdup("");
}

location copy_loc(location);
void free_location(location);

bool is_same_qualification(/* qualification */list, /*qualification*/list);
int compare_qualification(/* qualification */list, /*qualification*/list);

static inline void
extend_location_with(location source, location extension)
{ source->linenum2 = extension->linenum2;
  source->charnum2 = extension->charnum2;
}

static inline list cv_this_ptr(const clang::CXXMethodDecl* meth) {
  list /*specifier*/ qual = NULL;
  if (meth->isConst()) qual = cons_plain(CONST,qual);
  if (meth->isVolatile()) qual = cons_plain(VOLATILE,qual);
  return qual;
  }

static inline bool
isTemplateInstance(clang::TemplateSpecializationKind kind) {
  return clang::isTemplateInstantiation(kind);
}

namespace clang {
class Sema;
}

namespace Acsl {

class GlobalContext {
private:
  int _variableNumber;

public:
  class LogicVariable;
  class OverloadedLogicFunctions;
  class OverloadedLogicOperators;
  class LogicType;
  class LogicConstructor;
  class Qualification;
  class TemplateQualification;

  class NestedContext {
  private:
    NestedContext* _parent;
    std::string _name;

  public:
    NestedContext(const std::string& name) : _parent(NULL), _name(name) {}
    NestedContext(const NestedContext& source)
      : _parent(NULL), _name(source._name) {}
    virtual ~NestedContext() {}

    const std::string& getName() const { return _name; }
    enum Type
      { TUndefined, TLogicVariable, TOverloadedLogicFunctions,
        TLogicType, TLogicConstructor, TQualification, TTemplateQualification
      };
    virtual Type getType() const { return TUndefined; }
    bool isLogicVariable() const { return getType() == TLogicVariable; }
    bool isOverloadedLogicFunctions() const
      { return getType() == TOverloadedLogicFunctions; }
    bool isLogicType() const { return getType() == TLogicType; }
    bool isLogicConstructor() const { return getType() == TLogicConstructor; }
    bool isQualification() const { return getType() == TQualification; }
    bool isTemplateQualification() const
      { return getType() == TTemplateQualification; }

    LogicVariable& asLogicVariable();
    const LogicVariable& asLogicVariable() const;
    OverloadedLogicFunctions& asOverloadedLogicFunctions();
    const OverloadedLogicFunctions& asOverloadedLogicFunctions() const;
    LogicType& asLogicType();
    const LogicType& asLogicType() const;
    LogicConstructor& asLogicConstructor();
    const LogicConstructor& asLogicConstructor() const;
    Qualification& asQualification();
    const Qualification& asQualification() const;
    TemplateQualification& asTemplateQualification();
    const TemplateQualification& asTemplateQualification() const;

    NestedContext* sparent() const { return _parent; }
    void setParent(NestedContext* parent)
      { assert(!_parent); _parent = parent; }
    bool hasParent() const { return _parent != NULL; }
    bool hasSons() const 
      { return const_cast<NestedContext*>(this)->ssons() != NULL; }
       
    struct Less {
      bool operator()(const NestedContext* c1, const NestedContext* c2) const
        { if(!c1) return c2; // NULL is less than everything
          if(!c2) return false;
          return c1->compare(*c2) < 0;
        }
    };
    virtual int compare(const NestedContext& c) const
      { return this->_name.compare(c._name); }
    typedef std::set<NestedContext*, Less> SonsSet;
    virtual SonsSet* ssons() { return NULL; }
    SonsSet& sons()
      { SonsSet* result = ssons();
        assert(result);
        return *result;
      }
    const SonsSet& sons() const
      { SonsSet* result = const_cast<NestedContext*>(this)->ssons();
        assert(result);
        return *result;
      }
  };

private:
  NestedContext::SonsSet _logicTable;

  void init(); // add Utf8_logic::boolean

public:
  GlobalContext() : _variableNumber(0) { init(); }
  ~GlobalContext()
    { NestedContext::SonsSet::iterator iterEnd = _logicTable.end();
      for (NestedContext::SonsSet::iterator iter = _logicTable.begin();
          iter != iterEnd; ++iter)
        delete *iter;
    }

  int& variableNumber() { return _variableNumber; }
  const NestedContext::SonsSet& logicTable() const { return _logicTable; }
  NestedContext::SonsSet& logicTable() { return _logicTable; }
  NestedContext* find(const std::string& identifier, NestedContext* start)
      const;
  NestedContext* find(qualified_name identifier, NestedContext* start) const;
  NestedContext* findAbsolute(qualified_name identifier) const;
};
   
class GlobalContext::LogicVariable : public GlobalContext::NestedContext {
private:
  typedef NestedContext inherited;
  logic_var lvVariable;

public:
  LogicVariable(const std::string& name, logic_var variable)
    : inherited(name), lvVariable(variable) {}
  virtual ~LogicVariable() { free_logic_var(lvVariable); }
  virtual Type getType() const { return TLogicVariable; }
};

class GlobalContext::OverloadedLogicFunctions
    : public GlobalContext::NestedContext {
public:
  typedef std::list<std::pair<bool, logic_info> > Functions;

private:
  typedef NestedContext inherited;
  Functions _logicFunctions;
    // the first bool is the method flag

public:
  OverloadedLogicFunctions(const std::string& name, logic_info info,
      bool isMethod=false)
    : inherited(name)
    { _logicFunctions.push_back(std::make_pair(isMethod, info)); }
  virtual ~OverloadedLogicFunctions()
    { Functions::iterator iterEnd = _logicFunctions.end();
      for (Functions::iterator iter = _logicFunctions.begin();
          iter != iterEnd; ++iter)
        free_logic_info(iter->second);
    }
  virtual Type getType() const { return TOverloadedLogicFunctions; }
  virtual bool isOperator() const { return false; }
  OverloadedLogicOperators& asOperator();
  void addFunction(logic_info info, bool isMethod=false)
    { _logicFunctions.push_back(std::make_pair(isMethod, info)); }
  const Functions& getFunctions() const { return _logicFunctions; }
};

class GlobalContext::OverloadedLogicOperators
    : public GlobalContext::OverloadedLogicFunctions {
private:
  typedef GlobalContext::OverloadedLogicFunctions inherited;
  int _codeOperator;

public:
  OverloadedLogicOperators(const std::string& name, int codeOperator,
      logic_info info, bool isMethod=false)
    : inherited(name, info, isMethod), _codeOperator(codeOperator) {}
  virtual bool isOperator() const { return true; }
  int getCodeOperator() const { return _codeOperator; }
};

inline GlobalContext::OverloadedLogicOperators&
GlobalContext::OverloadedLogicFunctions::asOperator()
  { return (GlobalContext::OverloadedLogicOperators&) *this; }

class GlobalContext::LogicType : public GlobalContext::NestedContext {
private:
  typedef NestedContext inherited;
  logic_type_info _type;

public:
  LogicType(const std::string& name, logic_type_info type)
    : inherited(name), _type(type) {}
  virtual ~LogicType() { free_logic_type_info(_type); }
  virtual Type getType() const { return TLogicType; }
  logic_type_info type_info() const { return _type; }
};

class GlobalContext::LogicConstructor : public GlobalContext::NestedContext {
private:
  typedef NestedContext inherited;
  logic_ctor_info lciConstructor;

public:
  LogicConstructor(const std::string& name, logic_ctor_info constructor)
    : inherited(name), lciConstructor(constructor) {}
  virtual ~LogicConstructor() { free_logic_ctor_info(lciConstructor); }
  virtual Type getType() const { return TLogicConstructor; }
  logic_ctor_info getInfo() const { return lciConstructor; }
};

class GlobalContext::Qualification : public GlobalContext::NestedContext {
private:
  typedef NestedContext inherited;
  NestedContext::SonsSet mSons;
  tag_qualification tag;
  // + usings.

public:
  Qualification(const std::string& name, tag_qualification t)
    : inherited(name), tag(t) {}
  virtual ~Qualification()
    { NestedContext::SonsSet::iterator iterEnd = mSons.end();
      for (NestedContext::SonsSet::iterator iter = mSons.begin();
          iter != iterEnd; ++iter)
        delete *iter;
    }
  virtual Type getType() const { return TQualification; }
  virtual NestedContext::SonsSet* ssons() { return &mSons; }
  bool hasRecordType() const { return tag == QSTRUCTORCLASS; }
  bool hasTemplateRecordType() const { return tag == QTEMPLATEINSTANCE; }

  TemplateQualification* findInstance(/* template_parameter */ list parameters)
      const;
  qualified_name makeRecordName() const;
  /* qualification */ list makeQualificationList() const;
  qualification getQualification() const {
    const char* name = strdup(getName().c_str());
    switch(tag) {
      case QNAMESPACE:
        return qualification_QNamespace(name);
      case QSTRUCTORCLASS:
        return qualification_QStructOrClass(name);
      case QTEMPLATEINSTANCE:
        assert(false);
    }
    assert(false);
    return NULL;
  }
};

class GlobalContext::TemplateQualification
    : public GlobalContext::NestedContext {
private:
  typedef NestedContext inherited;
  NestedContext::SonsSet mSons;
  /* template_parameter */ list _parameters;
  friend class Qualification;
  friend class GlobalContext;

public:
  TemplateQualification(/* template_parameter */ list parameters)
    : inherited(""), _parameters(NULL)
    { /* template_parameter */ list* endParameters = &_parameters;
      while (parameters) {
        *endParameters = cons_container(template_parameter_dup(
          (template_parameter) parameters->element.container), NULL);
        endParameters = &((*endParameters)->next);
        parameters = parameters->next;
      };
    }
  virtual ~TemplateQualification()
    { while (_parameters) {
        free_template_parameter((template_parameter) _parameters
            ->element.container);
        /* template_parameter */ list temp = _parameters;
        _parameters = _parameters->next;
        free(temp);
      };
      NestedContext::SonsSet::iterator iterEnd = mSons.end();
      for (NestedContext::SonsSet::iterator iter = mSons.begin();
          iter != iterEnd; ++iter)
        delete *iter;
    }
  /* qualification */ list makeQualificationList() const;
  qualification getQualification(const char* name) const
    { /* template_parameter */ list parameters = _parameters;
      /* template_parameter */ list result = NULL;
      /* template_parameter */ list* endResult = &result;
      while (parameters) {
        *endResult = cons_container(template_parameter_dup((template_parameter)
            parameters->element.container), NULL);
        endResult = &(*endResult)->next;
        parameters = parameters->next;
      };
      return qualification_QTemplateInstance(name, result);
    }
  virtual int compare(const NestedContext& c) const;
  virtual Type getType() const { return TTemplateQualification; }
  virtual NestedContext::SonsSet* ssons() { return &mSons; }
  /* template_parameter */ list getParameters() const { return _parameters; }
  /* template_parameter */ list extractParameters()
    { list result = _parameters; _parameters = NULL; return result; }
};

inline GlobalContext::LogicVariable&
GlobalContext::NestedContext::asLogicVariable()
  { assert(getType() == TLogicVariable); return (LogicVariable&) *this; }
  
inline const GlobalContext::LogicVariable&
GlobalContext::NestedContext::asLogicVariable() const
  { assert(getType() == TLogicVariable); return (const LogicVariable&) *this; }
  
inline GlobalContext::OverloadedLogicFunctions&
GlobalContext::NestedContext::asOverloadedLogicFunctions()
  { assert(getType() == TOverloadedLogicFunctions);
    return (OverloadedLogicFunctions&) *this;
  }
  
inline const GlobalContext::OverloadedLogicFunctions&
GlobalContext::NestedContext::asOverloadedLogicFunctions() const
  { assert(getType() == TOverloadedLogicFunctions);
    return (const OverloadedLogicFunctions&) *this;
  }
  
inline GlobalContext::LogicType&
GlobalContext::NestedContext::asLogicType()
  { assert(getType() == TLogicType); return (LogicType&) *this; }
  
inline const GlobalContext::LogicType&
GlobalContext::NestedContext::asLogicType() const
  { assert(getType() == TLogicType); return (const LogicType&) *this; }
  
inline GlobalContext::LogicConstructor&
GlobalContext::NestedContext::asLogicConstructor()
  { assert(getType() == TLogicConstructor); return (LogicConstructor&) *this; }
  
inline const GlobalContext::LogicConstructor&
GlobalContext::NestedContext::asLogicConstructor() const
{ assert(getType() == TLogicConstructor);
  return (const LogicConstructor&) *this;
}
  
inline GlobalContext::Qualification&
GlobalContext::NestedContext::asQualification()
  { assert(getType() == TQualification); return (Qualification&) *this; }
  
inline const GlobalContext::Qualification&
GlobalContext::NestedContext::asQualification() const
  { assert(getType() == TQualification); return (const Qualification&) *this; }

inline GlobalContext::TemplateQualification&
GlobalContext::NestedContext::asTemplateQualification()
{ assert(getType() == TTemplateQualification);
  return (TemplateQualification&) *this;
}
  
inline const GlobalContext::TemplateQualification&
GlobalContext::NestedContext::asTemplateQualification() const
{ assert(getType() == TTemplateQualification);
  return (const TemplateQualification&) *this;
}

} // end of namespace Acsl

// Some smart constructors for intermediate AST

namespace Intermediate_ast {
  // the functions below duplicate the location and the string given as
  // argument, but not the AST nodes themselves.
  // Hence, caller has to ensure that such nodes are fresh.


  expression makeFloatConstant(const location loc, fkind k, const char* repr);

  expression makeIntLiteral(const location loc, ikind k, long value);

  expression makeStringLiteral(const location loc, const char* str);
 
  expression makeFloatZero(const location loc, fkind k);

  /* null pointer for an object type. */
  expression makeNullPointer(const location loc, qual_type pointee);

  /* unqualified and untemplated struct T type */
  qual_type makeStructType(qualified_name struct_name);
}

using namespace Intermediate_ast;

class FramacVisitor;

class RTTITable;
class ForwardReferenceList;
class Clang_utils {
public:
  class VirtualDeclRegistration {
  private:
    bool _doesRegisterDecl;

  protected:
    void setRegisterDecl() { _doesRegisterDecl = true; }
    void clearRegisterDecl() { _doesRegisterDecl = false; }

  public:
    VirtualDeclRegistration() : _doesRegisterDecl(false) {}
    VirtualDeclRegistration(const VirtualDeclRegistration& source)
      : _doesRegisterDecl(source._doesRegisterDecl) {}
    virtual ~VirtualDeclRegistration() {}

    bool doesRegisterDecl() const { return _doesRegisterDecl; }
    virtual void registerDecl(const clang::Decl* decl) {}
    virtual VirtualDeclRegistration* getNameRegistration() { return this; }
  };

private:
  mutable int _anonymousIdent;
  mutable std::map<const clang::Decl*, std::string> _anonymousMap;
  clang::ASTContext* _context;
  FramacVisitor* _caller;
  mutable Acsl::GlobalContext _acslContext;
  mutable std::vector<std::pair<const clang::Decl*, 
      const clang::TemplateArgumentList*> > _defaultTemplateInstances;

  bool _annotError;
  bool _doesGenerateImplicitMethods;
  bool _doesGenerateBareFunctions;
  bool _isVerbose;

  /// encapsulation of a method operating on plain (non-sugared) types
  template <typename T,
            T (Clang_utils::*builtinMethod) (clang::Type const*)const>
  class liftType {
    private:
    const Clang_utils* _clang_utils;
    public:
    T null;
    liftType(const Clang_utils* clang_utils, T dft):
      _clang_utils(clang_utils), null(dft) {}
    T operator()(const clang::Type* type) const {
        return (_clang_utils->*builtinMethod)(type);
    }
  };

  /// specialization of liftType for the case where the type is a
  /// C++ builtin-type
  template <typename T,
            T (Clang_utils::*builtinMethod) (clang::BuiltinType const*)const>
  class liftBuiltinType {
    private:
    const Clang_utils* _clang_utils;
    public:
    T null;
    liftBuiltinType(const Clang_utils* clang_utils, T dft):
      _clang_utils(clang_utils), null(dft) {}
    T operator()(const clang::Type* type) const {
      if (type->isBuiltinType())
        return
          (_clang_utils->*builtinMethod)(
            llvm::dyn_cast<clang::BuiltinType const>(type));
      return null;
    }
  };

  /// calls a given method on the given type after all possible desugaring
  /// (typedef, template instantiation, type inference, ... has been done.
  /// Op is supposed to be one of the two classes above
  template <typename T, class Op>
  T makeSpecificType(const Op* op, const clang::Type* type) const;

public:
  Clang_utils(clang::ASTContext*ctxt, FramacVisitor* caller)
    : _anonymousIdent(0), _anonymousMap(), _context(ctxt), _caller(caller),
      _annotError(false),_doesGenerateImplicitMethods(false),
      _doesGenerateBareFunctions(false),_isVerbose(false)
      { }

  location makeLocation(clang::SourceRange const& locs) const;
  // methods accessible for the debugger without any temp object on the stack
  location makeSingleLocation(clang::SourceLocation const& loc) const;
  location makeDeclLocation(clang::Decl const& decl) const;
  location makeExprLocation(clang::Expr const& expr) const;

  clang::SourceLocation getBeginLoc(clang::Stmt const& stmt) const {
#if CLANG_VERSION_MAJOR >= 8
    return stmt.getBeginLoc();
#else
    return stmt.getLocStart();
#endif
  }

  clang::SourceLocation getBeginLoc(clang::Decl const& d) const {
#if CLANG_VERSION_MAJOR >= 8
    return d.getBeginLoc();
#else
    return d.getLocStart();
#endif
  }

  clang::SourceLocation getBeginLoc(clang::CXXBaseSpecifier const& b) const {
#if CLANG_VERSION_MAJOR >= 8
    return b.getBeginLoc();
#else
    return b.getLocStart();
#endif
  }

  clang::SourceLocation getEndLoc(clang::Stmt const& stmt) const {
#if CLANG_VERSION_MAJOR >= 8
    return stmt.getEndLoc();
#else
    return stmt.getLocEnd();
#endif
  }

  clang::SourceLocation getEndLoc(clang::Decl const& d) const {
#if CLANG_VERSION_MAJOR >= 8
    return d.getEndLoc();
#else
    return d.getLocEnd();
#endif
  }

  void setAnnotError() { _annotError = true; }
  void setGenerateImplicitMethods() { _doesGenerateImplicitMethods = true; }
  void setGenerateBareFunctions() { _doesGenerateBareFunctions = true; }
  void setVerbose() { _isVerbose = true; }
  bool stopOnAnnotError () const { return _annotError; }
  bool doesGenerateImplicitMethods() const
    { return _doesGenerateImplicitMethods; }
  bool doesGenerateBareFunctions() const
    { return _doesGenerateBareFunctions; }
  bool isVerbose() const { return _isVerbose; }

  void pushTemplateInstance(const clang::Decl* templateDecl,
      const clang::TemplateArgumentList* instanceArguments)
    { _defaultTemplateInstances.push_back(
        std::make_pair(templateDecl, instanceArguments));
    }
  void popTemplateInstance(const clang::Decl* templateDecl)
    { assert(_defaultTemplateInstances.size() > 0
        && _defaultTemplateInstances.back().first == templateDecl);
      _defaultTemplateInstances.pop_back();
    }
  bool hasTemplateInstance() const
    { return _defaultTemplateInstances.size() > 0; }
  const clang::TemplateArgumentList* findInstanceArguments(
      const clang::Decl* templateDecl) const;
  const clang::TemplateArgument* findTemplateArgument(const std::string& name,
      const clang::NamedDecl*& templateParameter) const;
  Acsl::GlobalContext::NestedContext* queryDeclLogicScope(
      const clang::DeclContext* clangScope) const;

  void set_context(clang::ASTContext* ctxt) { _context = ctxt; }
  const clang::NamedDecl* findAnonymousDecl(const std::string& name) const;
  std::string findAnonymousName(const clang::NamedDecl* decl) const;

  // returns the fully qualified name of the declared identifier
  qualified_name makeQualifiedName(const clang::NamedDecl&,
      bool doesAcceptInstanceFail=false) const;
  signature makeSignature(const clang::FunctionDecl&) const;
  signature makeSignatureForMangling(const clang::FunctionDecl& function) const;

  // given a declaration context and a name, returns the corresponding
  // fully qualified name. name and decl cannot be NULL at the same time.
  qualified_name makeQualifiedName(const clang::DeclContext*Ctx,
      const char* name, const clang::NamedDecl* decl=NULL,
      tkind* templateParameters=NULL, bool doesAcceptInstanceFail=false) const;
  Acsl::GlobalContext& globalAcslContext() const { return _acslContext; }

  bool isIntegralType(clang::BuiltinType const* typ) const;
  bool isSignedType(clang::BuiltinType const* typ) const;
  bool isArithmeticType(clang::BuiltinType const* typ) const;
  bool isFloatingType(clang::BuiltinType const* typ) const;

  /// returns true if the type is directly a pointer.
  /// use isPointerType for desugaring the argument first.
  bool isPlainPointer(clang::Type const* typ) const;

  /// returns true if the type is directly a reference.
  /// use isReferenceType for desugaring the argument first
  bool isPlainReference(clang::Type const* typ) const;

  /// returns true if the type is directly an array.
  /// use isPlainArray for desugaring the argument first.
  bool isPlainArray(clang::Type const* typ) const;

  /// returns true if the expression is an lvalue with a reference type.
  /// we can't directly use expr->getType(), as the type of expressions
  /// is adjusted not to be a reference as per Clause 5[expr], §5
  bool lvalHasRefType(clang::Expr const* expr) const;

  bool is_lambda(clang::RecordDecl const* record) const;

  /*capture*/ list make_capture_list(
    clang::CXXRecordDecl::capture_const_range captures) const;

  typ make_lambda_type(
    clang::SourceLocation const& loc, clang::RecordDecl const* record,
    VirtualDeclRegistration* declRegistration=NULL) const;

  typ makeBuiltinType(
    clang::SourceLocation const& loc, clang::BuiltinType const* typ) const;
  typ makeBuiltinTypeNoLoc(clang::BuiltinType const* typ) const
    { return makeBuiltinType(clang::SourceLocation(),typ); }
 
  typ charType() const; /* plain char type (signedness depends on arch) */
  typ charPtrType() const; /* pointer to plain char. */

  qual_type charQualType() const { return qual_type_cons(NULL, charType()); }
  qual_type charPtrQualType() const {
    return qual_type_cons(NULL, charPtrType()); }

  logic_type makeBuiltinLogicType(
    clang::SourceLocation const& loc, clang::BuiltinType const* typ) const;
  typ makeArithmeticType(const clang::Type* type) const;

  ikind makePlainIntConstantType(const clang::Type* type) const;
  fkind makeFloatConstantType(const clang::BuiltinType* type) const;
  ikind makeIntConstantType(const clang::Type* type) const;
  fkind makeFloatConstantType(const clang::Type* type) const;

  typedef std::vector<const clang::Decl*> UnvisitedDecls;
  typ makePlainType(
    clang::SourceLocation const& loc,
    clang::QualType const& qt, 
    VirtualDeclRegistration* declRegistration=NULL, bool isPOD=false) const;
  qual_type makeType(
    clang::SourceLocation const& loc,
    clang::QualType const& qt,
    VirtualDeclRegistration* declRegistration=NULL) const;
  funkind cv_meth(const clang::CXXMethodDecl* meth) const
    { funkind result;
      if (meth->getKind() != clang::Decl::CXXConversion)
        result = funkind_FKMethod(cv_this_ptr(meth));
      else
        result =
          funkind_FKCastMethodOperator(
            cv_this_ptr(meth),
            makeType(
              meth->getLocation(),
              static_cast<const clang::CXXConversionDecl*>(meth)
                ->getConversionType()));
      return result;
    }
  qual_type makePODType(
    clang::SourceLocation const& loc, clang::QualType const& qt) const;
  logic_type makeLogicType(
    clang::SourceLocation const& loc, clang::Type const* type) const;
  logic_type makePointedType(
    clang::SourceLocation const& loc, clang::Type const* type) const;
  logic_type makeReferencedType(
    clang::SourceLocation const& loc, clang::Type const* type) const;
  logic_type makeElementArrayType(
    clang::SourceLocation const& loc, clang::Type const* type) const;
  qualified_name makeCompoundType(clang::Type const* type, tkind* templateKind)
      const;
  logic_type logicArithmeticPromotion(
    clang::SourceLocation const& loc, clang::Type const* type) const;
  bool isIntegralType(clang::Type const* type) const;
  bool isSignedType(clang::Type const* type) const;
  bool isArithmeticType(clang::Type const* type) const;
  bool isFloatingType(clang::Type const* type) const;
  bool isPointerType(clang::Type const* type) const;
  bool isReferenceType(clang::Type const* type) const;
  bool isArrayType(clang::Type const* type) const;

  bool isFunctionReferenceType(typ type) const;
  bool isObjectReferenceType(typ type) const;
  qual_type getObjectReferenceType(typ type) const;

  const clang::ConstantArrayType* isConstantArrayType(clang::Type const* type)
      const;
  bool retrieveTypeOfField(clang::Type const* type,
      const std::string& fieldName, term_offset& offset, logic_type& ltype,
      std::string& errorMessage, const clang::ASTContext* clangAST,
      clang::Sema* clangSema, const clang::SourceLocation& location,
      const RTTITable& rttiTable) const;
  template_parameter getTemplateExtension(
      const clang::SourceLocation & loc,
      const clang::TemplateArgument& parameter,
      /* template_parameter */ ForwardReferenceList& parametersList) const;
  /* template_parameter */ list getTemplateExtension(
      const clang::SourceLocation & loc,
      const clang::TemplateArgumentList& parameters) const;
  /* template_parameter */ list getTemplateExtension(
      const clang::ClassTemplateSpecializationDecl* inst) const
    { return
        getTemplateExtension(
          inst->getPointOfInstantiation(), inst->getTemplateArgs());
    }
   /* template_parameter */ list getTemplateExtension(
      const clang::FunctionTemplateSpecializationInfo* inst) const
    { return
        getTemplateExtension(
          inst->getPointOfInstantiation(), *inst->TemplateArguments);
    }
  const char* get_field_name(const clang::NamedDecl*) const;
  const char* get_aggregate_name(const clang::RecordDecl*,
      tkind* templateParameters) const;
  tkind makeTemplateKind(const clang::RecordDecl*) const;
  list /* specifier */ make_specifier_list(clang::QualType const& qt) const
    { list/*<specifier>*/ spec = NULL;
      if (qt.isLocalRestrictQualified())
        spec = cons_plain(RESTRICT,spec);
      if (qt.isLocalVolatileQualified())
        spec = cons_plain(VOLATILE,spec);
      if (qt.isLocalConstQualified())
        spec = cons_plain(CONST,spec);
      return spec;
    }

  int& logicVariableNumber() const { return _acslContext.variableNumber(); }

  static bool isExternCContext(const clang::DeclContext* ctx);

  std::string loc_as_string(const clang::SourceLocation& loc) const {
    return loc.printToString(_context->getSourceManager());
  }

  clang::SourceLocation getSourceLocation(const location loc) const {
    if (!loc) return clang::SourceLocation();
    const clang::SourceManager& sm = _context->getSourceManager();
#if CLANG_VERSION_MAJOR >= 10
    auto fileOpt = sm.getFileManager().getFileRef(std::string(loc->filename1));
    if (fileOpt) {
      const clang::FileEntry& file = fileOpt.get().getFileEntry();
      return sm.translateFileLineCol(&file, loc->linenum1, loc->charnum1);
    } else {
      // use dummy FileID if we don't have a valid FileEntry
      return sm.translateLineCol(clang::FileID(), loc->linenum1, loc->charnum1);
    }
#else
    const clang::FileEntry* file=sm.getFileManager().getFile(std::string(loc->filename1));
    return sm.translateFileLineCol(file,loc->linenum1,loc->charnum1);
#endif
  }

};

class ForwardList;
class ForwardReferenceList {
private:
  list* _front;
  list _back;
  friend class ForwardList;

public:
  ForwardReferenceList() : _front(NULL), _back(NULL) {}
  ForwardReferenceList(const ForwardReferenceList& source)
    : _front(source._front), _back(source._back) {}
  ForwardReferenceList& operator=(const ForwardReferenceList& source)
    { _front = source._front;
      _back = source._back;
      return *this;
    }
  ForwardReferenceList(list& alist) : _front(&alist), _back(alist)
    { while (_back && _back->next) _back = _back->next; }

  bool isValid() const
    { return _front && (!*_front ? !_back : (_back && !_back->next)); }

  void resetBack(list back)
    { _back = back;
      while (_back && _back->next) _back = _back->next;
    }
  void clear()
    { if (_front) {
        _back = *_front;
        while (_back && _back->next)
          _back = _back->next;
      }
      else
        _back = NULL;
    }
  void advanceToEnd()
    { if (_front) {
        if (!_back)
          _back = *_front;
        while (_back && _back->next)
          _back = _back->next;
      }
      else
        _back = NULL;
    }
  ForwardReferenceList& insertPlain(long value)
    { assert(_front);
      if (_back) {
        assert(!_back->next);
        _back->next = cons_plain(value, NULL);
        _back = _back->next;
      }
      else
        *_front = _back = cons_plain(value, NULL);
      return *this;
    }
  ForwardReferenceList& insertContainer(void* value)
    { assert(_front);
      if (_back) {
        assert(!_back->next);
        _back->next = cons_container(value, NULL);
        _back = _back->next;
      }
      else
        *_front = _back = cons_container(value, NULL);
      return *this;
    }
  ForwardReferenceList& append(ForwardReferenceList& tail)
    { assert(_front && tail._front);
      if (_back) {
        if (tail._back) {
          _back->next = *tail._front;
          _back = tail._back;
        };
      }
      else {
        *_front = *tail._front;;
        _back = tail._back;
      };
      return *this;
    }
  ForwardReferenceList& append(ForwardList& tail);
  list getBack() const { return _back; }
  list& getFront() const { assert(_front); return *_front; }
};

class ForwardDoubleReferenceList : public ForwardReferenceList {
private:
  list* _beforeBack;
  friend class ForwardList;

public:
  ForwardDoubleReferenceList() : _beforeBack(NULL) {}
  ForwardDoubleReferenceList(const ForwardDoubleReferenceList& source)
    : ForwardReferenceList(source), _beforeBack(NULL) {}
  ForwardDoubleReferenceList(list& alist) : ForwardReferenceList(alist),
      _beforeBack(NULL) {}
  ForwardDoubleReferenceList& operator=(const ForwardDoubleReferenceList& source)
    { ForwardReferenceList::operator=(source);
      _beforeBack = NULL;
      return *this;
    }

  void clear()
    { ForwardReferenceList::clear();
      _beforeBack = NULL;
    }
  void setBeforeBack(list* beforeBack) { _beforeBack = beforeBack; }
  ForwardDoubleReferenceList& insertPlain(long value)
    { if (getBack())
        _beforeBack = &getBack()->next;
      return (ForwardDoubleReferenceList&)
        ForwardReferenceList::insertPlain(value);
    }
  ForwardDoubleReferenceList& insertContainer(void* value)
    { if (getBack())
        _beforeBack = &getBack()->next;
      return (ForwardDoubleReferenceList&)
        ForwardReferenceList::insertContainer(value);
    }
  ForwardDoubleReferenceList& insertBeforeContainer(void* value)
    { if (_beforeBack) {
        list next = *_beforeBack;
        *_beforeBack = cons_container(value, NULL);
        (*_beforeBack)->next = next;
        _beforeBack = &(*_beforeBack)->next;
      }
      else {
        _beforeBack = &getBack()->next;
        ForwardReferenceList::insertContainer(value);
      };
      return *this;
    }
  ForwardDoubleReferenceList& append(ForwardReferenceList& tail)
    { _beforeBack = NULL;
      return (ForwardDoubleReferenceList&)
        ForwardReferenceList::append(tail);
    }
  ForwardDoubleReferenceList& append(ForwardList& tail)
    { _beforeBack = NULL;
      return (ForwardDoubleReferenceList&)
        ForwardReferenceList::append(tail);
    }
  list* getBeforeBack() const { return _beforeBack; }
};

class ForwardList {
private:
  list _front;
  list _back;

  friend ForwardReferenceList& ForwardReferenceList::append(ForwardList&);

public:
  ForwardList() : _front(NULL), _back(NULL) {}
  ForwardList(const ForwardList& source)
    : _front(source._front), _back(source._back) {}
  ForwardList& operator=(const ForwardList& source)
    { _front = source._front;
      _back = source._back;
      return *this;
    }
  bool isValid() const { return (!_front ? !_back : (_back && !_back->next)); }
  ForwardList& insertPlain(long value)
    { if (_back) {
        assert(!_back->next);
        _back->next = cons_plain(value, NULL);
        _back = _back->next;
      }
      else
        _front = _back = cons_plain(value, NULL);
      return *this;
    }
  ForwardList& insertContainer(void* value)
    { if (_back) {
        assert(!_back->next);
        _back->next = cons_container(value, NULL);
        _back = _back->next;
      }
      else
        _front = _back = cons_container(value, NULL);
      return *this;
    }
  ForwardList& append(const ForwardList& tail)
    { if (_back) {
        if (tail._front) {
          _back->next = tail._front;
          _back = tail._back;
        };
      }
      else {
        _front = tail._front;
        _back = tail._back;
      };
      return *this;
    }
  ForwardList& append(list tail)
    { ForwardReferenceList ftail(tail);
      if (_back) {
        if (tail) {
          _back->next = tail;
          _back = ftail._back;
        };
      }
      else {
        _front = tail;
        _back = ftail._back;
      };
      return *this;
    }
  list getFront() const { return _front; }
  // list getBack() const { return _back; }

  void clear() { _front = _back = NULL; }
};

inline ForwardReferenceList&
ForwardReferenceList::append(ForwardList& tail)
{ if (tail._front) {
    assert(_front);
    if (_back) {
      if (tail._back) {
        _back->next = tail._front;
        _back = tail._back;
      };
    }
    else {
      *_front = tail._front;;
      _back = tail._back;
    };
    tail._front = tail._back = NULL;
  };
  return *this;
}

/** @file */

class ForwardListOption {
private:
  option* _opt;
  ForwardReferenceList _content;

public:
  ForwardListOption() : _opt(NULL), _content() {}
  ForwardListOption(list& content) : _opt(NULL), _content(content) {}
  ForwardListOption(option& aopt): _opt(&aopt), _content()
    { if (aopt->is_some) {
        list l = (list)aopt->content.container;
        _content = ForwardReferenceList(l);
      }
    }
  bool isValid() const
    { return _opt ? ((*_opt)->is_some?_content.isValid():true)
                  : _content.isValid();
    }
  list getCore() const
    { assert(_content.isValid()); return _content.getBack(); }
  ForwardListOption& insertPlain(long value)
    { if (_opt && !(*_opt)->is_some) {
        (*_opt)->is_some = true;
        list* l = (list*)&(*_opt)->content.container;
        _content = ForwardReferenceList(*l);
      }
      _content.insertPlain(value);
      return *this;
    }
  
  ForwardListOption& insertContainer(void* value)
    { if (_opt && !(*_opt)->is_some) {
        (*_opt)->is_some = true;
        list* l = (list*)&(*_opt)->content.container;
        _content = ForwardReferenceList(*l);
      }
      _content.insertContainer(value);
      return *this;
    }
  ForwardReferenceList& getList()
    { if (_opt && !(*_opt)->is_some) {
        (*_opt)->is_some = true;
        list* l = (list*)&(*_opt)->content.container;
        _content = ForwardReferenceList(*l);
      }
      return _content;
    };
  const ForwardReferenceList& getCList() const
    { return _content; }
};

const char* mk_tmp_name ();
const char* mk_materialized_tmp_name ();
bool isRecordOrRecordRef(const clang::Type* type);


#endif //Clang_utilsH
