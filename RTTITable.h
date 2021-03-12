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
//   Definition of pointers for Virtual Method Tables
//

#ifndef Table_RTTIH
#define Table_RTTIH

#ifdef __GNUC__
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wclass-memaccess"
#endif
#include <list>
#include "clang/AST/DeclCXX.h"
#ifdef __GNUC__
#pragma GCC diagnostic pop
#endif

#include "Clang_utils.h"

extern "C" {
#include "intermediate_format.h"
}

class RTTITable {
public:
  typedef std::vector<std::pair<const clang::CXXRecordDecl*, int> >
    InheritancePath;
  typedef std::pair<const clang::CXXRecordDecl*, int> VirtualInheritancePath;
  typedef std::vector<std::pair<const clang::CXXRecordDecl*, int> >
    InheritancePosition;
  typedef std::vector<int> VirtualInheritancePosition;

private:
  class ClassInfo {
  private:
    class VirtualMethodInfo {
    private:
      const clang::CXXMethodDecl* _method;
      InheritancePath _inheritancePath;
      VirtualInheritancePath _virtualInheritancePath;
      InheritancePath _parentInheritancePath;

    public:
      VirtualMethodInfo()
        : _method(NULL), _virtualInheritancePath(
            std::make_pair((const clang::CXXRecordDecl*) NULL, 0)) {}
         // shift for virtual base class access
         // _virtualInheritancePath.second is the index in _virtualMethodTable
      VirtualMethodInfo(const clang::CXXMethodDecl* method)
        : _method(method),
          _virtualInheritancePath(
            std::make_pair((const clang::CXXRecordDecl*) NULL, 0))
        {}
      VirtualMethodInfo(const VirtualMethodInfo& source)
        : _method(source._method), _inheritancePath(source._inheritancePath),
          _virtualInheritancePath(source._virtualInheritancePath),
          _parentInheritancePath(source._parentInheritancePath) {}
      VirtualMethodInfo& operator=(const VirtualMethodInfo& source)
        { _method = source._method;
          _inheritancePath = source._inheritancePath;
          _virtualInheritancePath = source._virtualInheritancePath;
          _parentInheritancePath = source._parentInheritancePath;
          return *this;
        }

      bool isValid() const
        { return _method
            || (_virtualInheritancePath.first && _inheritancePath.empty());
        }
      bool isMethod() const { return _method != NULL; }
      bool isVirtualBaseAccess() const { return _method == NULL; }
      const clang::CXXMethodDecl* getMethod() const { return _method; }
      void setMethod(const clang::CXXMethodDecl* method) { _method = method; }
      void addInherits(const clang::CXXRecordDecl* baseClass, int vmtPosition)
        { if (!_virtualInheritancePath.first)
            _inheritancePath.push_back(
              std::make_pair(baseClass, vmtPosition));
          else {
            _virtualInheritancePath.second += vmtPosition;
            _parentInheritancePath.push_back(
              std::make_pair(baseClass, vmtPosition));
          };
        }
      void setVirtualInherits(const clang::CXXRecordDecl* baseClass,
          int vmtPosition)
        { if (!_virtualInheritancePath.first)
            _virtualInheritancePath = std::make_pair(baseClass, vmtPosition);
          else
            _virtualInheritancePath.second += vmtPosition+1;
          _parentInheritancePath.clear();
        }
      bool hasVirtualInheritancePath() const
        { return _virtualInheritancePath.first; }
      const InheritancePath& getInheritancePath() const
        { return _inheritancePath; }
      const InheritancePath& getParentInheritancePath() const
        { return _parentInheritancePath; }
      const VirtualInheritancePath& getVirtualInheritancePath() const
        { assert(_virtualInheritancePath.first);
          return _virtualInheritancePath;
        }
    };

    std::vector<VirtualMethodInfo> _virtualMethodTable;
    std::vector<const clang::CXXRecordDecl*> _virtualBaseClassTable;
    InheritancePosition _derivationsPosition;
    VirtualInheritancePosition _virtualDerivationsPosition;
    int _firstMultiplePosition;
    InheritancePath _pvmtAccess;
      // when _firstMultiplePosition == -1
    friend class RTTITable;

  public:
    ClassInfo() : _firstMultiplePosition(0) {}

    typedef std::vector<VirtualMethodInfo>::const_iterator MethodIterator;
    bool isSameMethod(const clang::CXXMethodDecl* first,
                      const clang::CXXMethodDecl* second) const;
    bool hasSameSignature(const clang::CXXMethodDecl* first,
                          const clang::CXXMethodDecl* second) const;
    int addDerivation(const ClassInfo& source,
        const clang::CXXRecordDecl* base, bool isVirtual);
    bool hasVirtualBaseClasses() const
      { return !_virtualBaseClassTable.empty(); }
    bool hasVirtualMethods() const
      { return !_virtualMethodTable.empty(); }
    const std::vector<const clang::CXXRecordDecl*>& getVirtualBases() const
      { return _virtualBaseClassTable; }
    int numberOfMethods() const { return _virtualMethodTable.size(); }
    int addVirtualMethod(const clang::CXXMethodDecl* method);
    int getIndexOfMethod(const clang::CXXMethodDecl* method,
        const InheritancePath*& inheritancePath,
        const VirtualInheritancePath*& virtualInheritancePath) const;
    int getBasePosition(const clang::CXXRecordDecl* base, bool& isVirtual)
        const;
    bool isVirtualBase(const clang::CXXRecordDecl* base) const
      { bool result = false;
        if (!_virtualBaseClassTable.empty()) {
          std::vector<const clang::CXXRecordDecl*>::const_iterator
            iter = _virtualBaseClassTable.begin(),
            iterEnd = _virtualBaseClassTable.end();
          for (; !result && iter != iterEnd; ++iter)
            result = *iter == base;
        };
        return result;
      }
    bool isEmpty() const {
      return
        _virtualMethodTable.empty() &&
        _virtualBaseClassTable.empty() &&
        _derivationsPosition.empty(); }
    bool hasPvmtAsFirstField() const { return _firstMultiplePosition >= 0; }
    const InheritancePath& getPvmtField() const
      { assert(_firstMultiplePosition == -1);
        return _pvmtAccess;
      }

    MethodIterator beginOfMethods() const
      { return _virtualMethodTable.begin(); }
    MethodIterator endOfMethods() const { return _virtualMethodTable.end(); }
    void swap(ClassInfo& source)
      { _virtualMethodTable.swap(source._virtualMethodTable);
        _virtualBaseClassTable.swap(source._virtualBaseClassTable);
        _derivationsPosition.swap(source._derivationsPosition);
        _virtualDerivationsPosition.swap(source._virtualDerivationsPosition);
      }
  };

  class DelayedMethodCalls {
  private:
    class MethodCall {
    private:
      clang::CXXMethodDecl* _method;
      clang::CXXRecordDecl* _base;
      std::vector<std::pair<int64_t*,
          std::pair</* inheritance */ list*, /* inheritance */ list*> > >
        _indexShiftObject;

    public:
      MethodCall(clang::CXXMethodDecl* method, int64_t* methodIndex,
        /* inheritance */ list* shiftObject, /* inheritance */ list* shiftPvmt)
        : _method(method), _base(NULL)
        { _indexShiftObject.push_back(std::make_pair(methodIndex,
            std::make_pair(shiftObject, shiftPvmt)));
        }
      MethodCall(clang::CXXRecordDecl* virtualBase, int64_t* subClassIndex)
        : _method(NULL), _base(virtualBase)
        { _indexShiftObject.push_back(std::make_pair(subClassIndex,
              std::pair<list*, list*>(NULL, NULL)));
        }

      void add(int64_t* methodIndex, /* inheritance */ list* shiftObject,
          /* inheritance */ list* shiftPvmt)
        { assert(_method && !_base);
          _indexShiftObject.push_back(std::make_pair(methodIndex,
            std::make_pair(shiftObject, shiftPvmt)));
        }
      void add(int64_t* accessIndex)
        { assert(_base && !_method);
          _indexShiftObject.push_back(std::make_pair(accessIndex,
              std::pair<list*, list*>(NULL, NULL)));
        }
      bool isValid() const { return _method ? !_base : (bool) _base; }
      void apply(const Clang_utils& utils, const ClassInfo& methodTable);
      bool isVirtualMethod() const { return _method; }
      bool isBaseAccess() const { return _base; }
      clang::CXXMethodDecl* getMethod() const { return _method; }
      clang::CXXRecordDecl* getBaseAccess() const { return _base; }
    };
    std::vector<MethodCall> _delayedCalls;

  public:
    DelayedMethodCalls() {}

    void addMethodCall(clang::CXXMethodDecl* method, int64_t* methodIndex,
        /* inheritance */ list* shiftObject, /* inheritance */ list* shiftPvmt);
    void addFieldAccess(clang::CXXRecordDecl* baseClass,
        int64_t* accessIndex);
    void updateWith(const Clang_utils& utils, const ClassInfo& methodTable);
  };

private:
  bool _hasInitRTTIFunctions;
  std::map<const clang::CXXRecordDecl*, ClassInfo> _classInfoTable;
  std::list<const clang::CXXRecordDecl*> _currentClass;
  std::list<ClassInfo> _currentClassInfo;
  std::list<std::vector<list*> > _pvmtInsertionPoints;
  std::vector<bool*> _virtualTags;
  std::map<const clang::CXXRecordDecl*, DelayedMethodCalls> _delayedMethodCalls;

  /* creates a fully qualified name for the special member of the
     current class. */
  qualified_name specialMemberName(
    const Clang_utils& utils,const char* base) const;

  void insertVMTContentPrelude(ForwardReferenceList& globals, location loc);
  void insertVMTTypePrelude(ForwardReferenceList& globals, location loc);
  void insertRTTIInfoPrelude(ForwardReferenceList& globals, location loc);
  /* statement */ list* insertRTTIAlgorithmsAuxDeclPrelude(
      ForwardReferenceList& globals, location loc);
  /* statement */ list* insertRTTIAlgorithmsAuxWhilePrelude(
      /* statement */ list* functionBodyRef, location loc);
  void insertRTTIAlgorithmsAuxWhileBodyPrelude(/* statement */ list*
      whileBodyRef, location loc, /* statement */ list*& then,
      /* statement */ list*& elseThen, /* statement */ list*& elseElseThen);
  void insertRTTIAlgorithmsAuxWhileThenBodyPrelude(/* statement */ list*
      statements, location loc);
  void insertRTTIAlgorithmsAuxWhileElseThenBodyPrelude(/* statement */ list*
      statements, location loc);
  void insertRTTIAlgorithmsAuxWhileElseElseThenBodyPrelude(
      /* statement */ list* statements, location loc);
  /* statement */ list* insertRTTIAlgorithmsAuxPrelude(
      ForwardReferenceList& globals, location loc);
  /* statement */ list* insertRTTIAlgorithmsDeclPrelude(
      ForwardReferenceList& globals, location loc);
  /* statement */ list* insertRTTIAlgorithmsFirstPartPrelude(
      /* statement */ list* statements, location loc);
  /* statement */ list* insertRTTIAlgorithmsDoWhilePrelude(
      /* statement */ list*& statements, location loc);
  /* statement */ list* insertRTTIAlgorithmsSecondWhilePrelude(
      /* statement */ list*& statements, location loc);
  void insertRTTIAlgorithmsSecondWhileBodyPrelude(/* statement */ list*&
      statements, location loc);
  /* statement */ list* insertRTTIAlgorithmsSecondIfThenPrelude(
      /* statement */ list*& statements, location loc);
  void insertRTTIAlgorithmsSecondIfThenBodyPrelude(/* statement */ list*&
      statements, location loc);
  void insertRTTIAlgorithmsLastPartPrelude(/* statement */ list*& statements,
      location loc);
  /* statement */ list* insertRTTIAlgorithmsPrelude(
      ForwardReferenceList& globals, location loc);
  void insertRttiPrelude(ForwardReferenceList& globals, location loc);

  void insertStaticVMTDeclaration(ForwardReferenceList& classContent,
      location classLoc);
  qualified_name insertStaticVMTDefinition(const Clang_utils& utils,
      ForwardReferenceList& globals, location classLoc);

  void insertStaticBaseClassesDeclaration(ForwardReferenceList& classContent,
      location classLoc);
  qualified_name insertStaticBaseClassesDefinition(const Clang_utils& utils,
      ForwardReferenceList& globals, location classLoc);

  void insertStaticRTTIDeclaration(ForwardReferenceList& classContent,
      location classLoc);
  qualified_name insertStaticRTTIDefinition(const Clang_utils& utils,
      ForwardReferenceList& globals, location classLoc,
      qualified_name vmtName, qualified_name nameBaseClasses);
  void insertStaticEmptyRTTIDefinition(
    const Clang_utils& utils, ForwardReferenceList& globals, location classLoc);

  void insertStaticVMTHeaderDeclaration(ForwardReferenceList& classContent,
      location classLoc);
  void insertDeclStaticVMTHeaderDefinition(ForwardReferenceList& globals,
      location classLoc, qualified_name vmtName);
  void insertStaticVMTHeaderDefinition(const Clang_utils& utils,
      ForwardReferenceList& globals, location classLoc, qualified_name vmtName,
      qualified_name nameRtti);

  bool retrieveStaticInheritancePathBetween(const clang::CXXRecordDecl* derived,
      const clang::CXXRecordDecl* base, InheritancePath& result,
      const Clang_utils& utils,
      VirtualInheritancePath* virtualResult = NULL) const;

public:
  RTTITable()
    : _hasInitRTTIFunctions(false), _currentClass(), _currentClassInfo(),
      _pvmtInsertionPoints() {}

  bool hasDelayedMethodCalls() const
    { return !_delayedMethodCalls.empty(); }
  void insertVMTAndRttiPrelude(ForwardReferenceList& globals, location loc);
  void enterClass(const clang::CXXRecordDecl* classDecl)
   { _currentClass.push_front(classDecl);
     _currentClassInfo.push_front(ClassInfo());
     _pvmtInsertionPoints.push_front(std::vector<list*>());
    }
  const clang::CXXRecordDecl* getCurrentClass() const
    { return _currentClass.empty()?NULL:_currentClass.front(); }
  const ClassInfo* getCurrentClassInfo() const
    { return _currentClassInfo.empty()?NULL:&_currentClassInfo.front(); }
  void addBareToQualification(qualified_name& name) const;

  /* just pop the class stack. */
  void exitClass() {
    _currentClass.pop_front();
    _currentClassInfo.pop_front();
    _pvmtInsertionPoints.pop_front();
    _virtualTags.pop_back();
  }
  
  /* pop the class stack and generates appropriate vmt bindings if needed. */
  void exitClass(const Clang_utils& utils, ForwardReferenceList& content,
      ForwardReferenceList& globals, location classLoc);

  expression getPvmt(const Clang_utils& utils,
      const clang::CXXRecordDecl* source, expression arg) const;
  void addPvmtSetter(/* statement */ list& insertionPoint)
    { _pvmtInsertionPoints.front().push_back(&insertionPoint); }
  void addPvmtSetter(const Clang_utils& utils,
    const clang::CXXRecordDecl* source, /* statement */ list& insertionPoint,
    location loc);
  void addBarePvmtSetter(const Clang_utils& utils,
    const clang::CXXRecordDecl* source, /* statement */ list& insertionPoint,
    location loc);
  void addPvmtSetterForBare(const Clang_utils& utils,
    const clang::CXXRecordDecl* source, /* statement */ list& insertionPoint,
    location loc);
  /* return the position in the vmt - result is negative for virtual derivation
   */
  int addDerivation(const clang::CXXRecordDecl* source, bool isVirtual)
  { assert(!_currentClassInfo.empty());
    std::map<const clang::CXXRecordDecl*, ClassInfo>::const_iterator
      found = _classInfoTable.find(source);
    if (found == _classInfoTable.end())
      found = _classInfoTable.insert(std::make_pair(source, ClassInfo()))
          .first;
    // add the base class to the current _derivationsPosition list
    int res =
      _currentClassInfo.front().addDerivation(found->second, source, isVirtual);
    return !found->second.isEmpty() ? res : 0;
  }
  bool hasVirtualMethods() const
  { return _currentClassInfo.front().numberOfMethods() > 0; }

  bool hasVirtualBaseClasses(const clang::CXXRecordDecl* source) const
  { const ClassInfo* info = getClassInfo(source);
    return info && info->hasVirtualBaseClasses();
  }
  bool hasPvmt(const clang::CXXRecordDecl* source) const
  { std::map<const clang::CXXRecordDecl*, ClassInfo>::const_iterator
      found = _classInfoTable.find(source);
    return (found != _classInfoTable.end()) && !found->second.isEmpty();
  }
  bool hasVirtualMethods(const clang::CXXRecordDecl* source) const
  { std::map<const clang::CXXRecordDecl*, ClassInfo>::const_iterator
      found = _classInfoTable.find(source);
    return (found != _classInfoTable.end())
        && found->second.numberOfMethods() > 0;
  }
  const ClassInfo* getClassInfo(const clang::CXXRecordDecl* source) const
  { if (getCurrentClass() == source)
      return getCurrentClassInfo();
    std::map<const clang::CXXRecordDecl*, ClassInfo>::const_iterator
      found = _classInfoTable.find(source);
    const ClassInfo* sourceInfo = NULL;
    if (found != _classInfoTable.end())
      sourceInfo = &found->second;
    else {
      assert(_currentClass.size() == _currentClassInfo.size());
      std::list<const clang::CXXRecordDecl*>::const_iterator
        currentClassIter = _currentClass.begin(),
        currentClassIterEnd = _currentClass.end();
      std::list<ClassInfo>::const_iterator
        currentClassInfoIter = _currentClassInfo.begin(),
        currentClassInfoIterEnd = _currentClassInfo.end();
      for (; !sourceInfo && currentClassIter != currentClassIterEnd;
            ++currentClassIter) {
        assert(currentClassInfoIter != currentClassInfoIterEnd);
        if (*currentClassIter == source)
          sourceInfo = &*currentClassInfoIter;
        ++currentClassInfoIter;
      };
      assert(sourceInfo || currentClassInfoIter == currentClassInfoIterEnd);
    };
    return sourceInfo;
  }
  
  int getBasePosition(const clang::CXXRecordDecl* derived,
      const clang::CXXRecordDecl* base, bool& isVirtual) const
    { std::map<const clang::CXXRecordDecl*, ClassInfo>::const_iterator
        found = _classInfoTable.find(derived);
      int result = -1;
      int oldVirtual = isVirtual;
      if (found != _classInfoTable.end() &&
          (!found->second.isEmpty() || found->second.hasVirtualBaseClasses())) {
        result = found->second.getBasePosition(base, isVirtual);
        assert(oldVirtual == isVirtual);
      }
      else {
        assert(_currentClass.size() == _currentClassInfo.size());
        std::list<const clang::CXXRecordDecl*>::const_iterator
          currentClassIter = _currentClass.begin(),
          currentClassIterEnd = _currentClass.end();
        std::list<ClassInfo>::const_iterator
          currentClassInfoIter = _currentClassInfo.begin(),
          currentClassInfoIterEnd = _currentClassInfo.end();
        bool hasResult = false;
        for (; !hasResult &&
               currentClassIter != currentClassIterEnd &&
               currentClassInfoIter != currentClassInfoIterEnd;
              ++currentClassIter, ++currentClassInfoIter) {
          if (*currentClassIter == derived) {
            hasResult = true;
            result = currentClassInfoIter->getBasePosition(base, isVirtual);
            assert(oldVirtual == isVirtual);
          };
        };
      };
      return result;
    }
  void addVirtualMethod(const clang::CXXMethodDecl* method)
    { assert(!_currentClass.empty() && !_virtualTags.empty());
      _currentClassInfo.front().addVirtualMethod(method);
      *_virtualTags.back() = true;
    }
  void setVirtualTag(bool& virtualTag) { _virtualTags.push_back(&virtualTag); }
  void retrieveMethodIndex(const Clang_utils& utils,
      const clang::CXXRecordDecl* classCaller,
      clang::CXXMethodDecl* methodCalled,
      int64_t* methodIndex, /* inheritance */ list* shiftObject,
      /* inheritance */ list* shiftPvmt);
  void retrieveBaseIndex(const Clang_utils& utils,
      const clang::CXXRecordDecl* classCaller,
      clang::CXXRecordDecl* baseClass, int64_t* accessIndex);

  /*! return the canonical inheritance path from derived to base. There are 4
    possibilities:
    - no such path exists: result and virtualResult will be left untouched.
    - the path is completely static: result will contain the resulting path
    - base is a virtual base of derived: virtualResult will contain the
      information to compute the offset from derived to base. result will be
      empty.
    - base is a (non-virtual) base of a virtual base of derived:
      both virtualResult and result will be filled as described above.
   */
  void retrieveInheritancePathBetween(const clang::CXXRecordDecl* derived,
      const clang::CXXRecordDecl* base, InheritancePath& result,
      VirtualInheritancePath& virtualResult,
      const Clang_utils& utils) const;
};

#endif // Table_RTTIH

/*
Local Variables:
mode: c++
End:
*/
