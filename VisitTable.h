/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-Clang                                      */
/*                                                                        */
/*  Copyright (C) 2012-2018                                               */
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
//   Definition of VisitTable
//

#ifndef Visit_TableH
#define Visit_TableH

#include "clang/AST/DeclCXX.h"
#include "Clang_utils.h"

extern "C" {
#include "intermediate_format.h"
}

class VisitTable {
public:
  class KeyInfo {
  private:
    const clang::Decl* _key;
    friend class VisitTable;

  public:
    KeyInfo(const clang::Decl* key) : _key(key) {}
    KeyInfo(const KeyInfo& source) : _key(source._key) {}
    virtual ~KeyInfo() {}
    virtual bool isSubKey() const { return false; }
    virtual bool isMissingDecl() const { return false; }
    virtual bool isGenerationMissing() const { return false; }
    virtual bool isClassGenerationMissing() const { return false; }
    virtual bool isInstanceClass() const { return false; }
    virtual bool isFunctionGenerationMissing() const { return false; }
    virtual bool replaceWaitingBy(const clang::Decl* oldDecl,
        const std::vector<const clang::Decl*>& newDecls)
      { assert(false); return true; }
    virtual bool solve(const clang::Decl* decl, ForwardReferenceList& globals,
        VisitTable& table) { assert(false); return false; }
    virtual bool isComplete() const { return true; }
    virtual void print(std::ostream& out) const
      { const clang::NamedDecl* decl = llvm::dyn_cast<clang::NamedDecl>
            (_key);
        if (decl)
          out << decl->getNameAsString() << ": ";
        else
          out << "clang_unnamed: ";
      }
    const clang::Decl* key() const { return _key; }

    class Less {
    public:
      bool operator()(const KeyInfo* first, const KeyInfo* second) const
        { return first->_key < second->_key; }
    };
  };

  class SubKeyInfo : public KeyInfo {
  private:
    const clang::Decl* _root;
    std::vector<const clang::Decl*> _specificWaitDeclarations;

  public:
    SubKeyInfo(const clang::Decl* key, const clang::Decl* root,
        std::vector<const clang::Decl*>& specificWaitDeclarations)
      : KeyInfo(key), _root(root)
      { _specificWaitDeclarations.swap(specificWaitDeclarations); }
    SubKeyInfo(const clang::Decl* key, const clang::Decl* root)
      : KeyInfo(key), _root(root) {}
    SubKeyInfo(const SubKeyInfo& source)
      : KeyInfo(source), _root(source._root),
        _specificWaitDeclarations(source._specificWaitDeclarations) {}

    virtual bool isSubKey() const { return true; }
    const clang::Decl* root() const { return _root; }
    const std::vector<const clang::Decl*>& getSpecificWaitDeclarations() const
      { return _specificWaitDeclarations; }
    void addSpecificWaitDeclarations(
        const std::vector<const clang::Decl*>& waitDeclarations)
      { if (!waitDeclarations.empty()) {
          if (_specificWaitDeclarations.empty())
            _specificWaitDeclarations = waitDeclarations;
          else {
            std::vector<const clang::Decl*>::const_iterator
              sourceIterEnd = waitDeclarations.end(),
              sourceIter = waitDeclarations.begin();
            for (; sourceIter != sourceIterEnd; ++sourceIter) {
              const clang::Decl* declToInsert = *sourceIter;
              bool hasFound = false;
              std::vector<const clang::Decl*>::const_iterator
                iterEnd = _specificWaitDeclarations.end(),
                iter = _specificWaitDeclarations.begin();
              for (; !hasFound && iter != iterEnd; ++iter)
                hasFound = *iter == declToInsert;
              if (!hasFound)
                _specificWaitDeclarations.push_back(declToInsert);
            };
          };
        };
      }
  };

  class MissingFunctionGeneration : public KeyInfo {
  private:
    translation_unit_decl _waitingFunDefinition;
    translation_unit_decl _waitingAdditionalFunDefinition; /* may be NULL */
    std::vector<const clang::Decl*> _waitDeclarations;
    friend class VisitTable;

  public:
    MissingFunctionGeneration(const clang::FunctionDecl* key,
        translation_unit_decl waitingDefinition,
        translation_unit_decl waitingAdditionalDefinition=NULL)
      : KeyInfo(key), _waitingFunDefinition(waitingDefinition),
        _waitingAdditionalFunDefinition(waitingAdditionalDefinition) {}
    virtual ~MissingFunctionGeneration()
      { if (_waitingFunDefinition) {
          free_translation_unit_decl(_waitingFunDefinition);
          _waitingFunDefinition = NULL;
        };
        if (_waitingAdditionalFunDefinition) {
          free_translation_unit_decl(_waitingAdditionalFunDefinition);
          _waitingAdditionalFunDefinition = NULL;
        };
      }
    
    const std::vector<const clang::Decl*>& waitDeclarations() const
      { return _waitDeclarations; }
    virtual bool isComplete() const
      { return !_waitingFunDefinition && _waitDeclarations.empty(); }
    virtual void print(std::ostream& out) const;
    virtual bool isGenerationMissing() const { return true; }
    virtual bool isFunctionGenerationMissing() const { return true; }
    virtual bool solve(const clang::Decl* decl, ForwardReferenceList& globals,
        VisitTable& table);
    virtual bool replaceWaitingBy(const clang::Decl* oldDecl,
        const std::vector<const clang::Decl*>& newDecls);
  };

  class MissingSubClassGeneration {
  private:
    const clang::Decl* _key;
    class_decl _waitingSubClassDecl;
    std::vector<const clang::Decl*> _additionalWaitDeclarations;
    std::vector<MissingSubClassGeneration> _subGenerations;
    std::set<const clang::Decl*> _subWaitDeclarations;
    int _parentPosition;
    friend class VisitTable;

  public:
    MissingSubClassGeneration(const clang::RecordDecl* key,
        class_decl waitingSubClassDecl, int parentPosition)
      : _key(key), _waitingSubClassDecl(waitingSubClassDecl),
        _parentPosition(parentPosition) {}

    void addWaitFor(const clang::Decl* decl)
      { _additionalWaitDeclarations.push_back(decl); }
    MissingSubClassGeneration& createSubDeclaration(
        const clang::RecordDecl* key, class_decl waitingSubClassDecl)
      { int position = 0;
        assert(_waitingSubClassDecl
          && _waitingSubClassDecl->tag_class_decl == CCOMPOUND
          && _waitingSubClassDecl->cons_class_decl.CCompound.body->is_some);
        /* class_decl */ list parentList = (list) _waitingSubClassDecl
          ->cons_class_decl.CCompound.body->content.container;
        while (parentList) {
          ++position;
          parentList = parentList->next;
        };
        _subGenerations.push_back(MissingSubClassGeneration(key,
            waitingSubClassDecl, position + _subGenerations.size()));
        return _subGenerations.back();
      }
    const std::vector<const clang::Decl*>& waitDeclarations() const
      { return _additionalWaitDeclarations; }
    std::vector<const clang::Decl*>& waitDeclarations()
      { return _additionalWaitDeclarations; }
    bool removeWait(const clang::Decl* decl);
    bool removeWaitWithinClass(const clang::Decl* decl,
        /* class_decl */ list*& cursor, /* class_decl */ list* parentDeclList,
        int& cursorIndex, int targetIndex)
      { assert(_waitingSubClassDecl
          && _waitingSubClassDecl->tag_class_decl == CCOMPOUND
          && _waitingSubClassDecl->cons_class_decl.CCompound.body->is_some);
        class_decl subContent = _waitingSubClassDecl;
        bool result = removeWait(decl);
        if (result) {
          assert(targetIndex >= 0);
          if (cursor == NULL || cursorIndex > targetIndex) {
            cursor = parentDeclList;
            cursorIndex = 0;
          }
          while (cursorIndex < targetIndex) {
            ++cursorIndex;
            cursor = &(*cursor)->next;
          }
          list next = *cursor;
          *cursor = cons_container(subContent, next);
        };
        return result;
      }
#if 0
    bool solve(const clang::Decl* decl, MissingClassGeneration& parentDecl,
        ForwardReferenceList& globals, VisitTable& table);
#endif
    void print(std::ostream& out, bool ident=1) const;
    bool replaceWaitingBy(const clang::Decl* oldDecl,
        const std::vector<const clang::Decl*>& newDecls);
    class_decl getWaitingSubClassDecl() const { return _waitingSubClassDecl; }
    bool setAsComplete(ForwardReferenceList& classDeclList)
      { assert(_waitingSubClassDecl);
        bool result;
        if (_additionalWaitDeclarations.empty()) {
          classDeclList.insertContainer(_waitingSubClassDecl);
          _waitingSubClassDecl = NULL;
          result = true;
        }
        else
          result = false;
        if (!_subGenerations.empty()) {
          std::vector<MissingSubClassGeneration>::const_iterator
            subIterEnd=_subGenerations.end(), subIter=_subGenerations.begin();
          for (; subIter != subIterEnd; ++subIter) {
            _subWaitDeclarations.insert(subIter->_additionalWaitDeclarations.begin(),
              subIter->_additionalWaitDeclarations.end());
            _subWaitDeclarations.insert(subIter->_subWaitDeclarations.begin(),
              subIter->_subWaitDeclarations.end());
          };
        };
        return result;
      }
    /* class_decl */ list& getContent() const
      { assert(_waitingSubClassDecl->tag_class_decl==CCOMPOUND);
        return *(/* class_decl */ list*) &_waitingSubClassDecl
          ->cons_class_decl.CCompound.body->content.container;
      }
    const clang::Decl* key() const { return _key; }
    const std::vector<const clang::Decl*>* findSubClassDependencies(
        const clang::Decl* subClass) const
      { const std::vector<const clang::Decl*>* result = NULL;
        std::vector<MissingSubClassGeneration>::const_iterator
          subIter = _subGenerations.begin(), subIterEnd = _subGenerations.end();
        for (; !result && subIter != subIterEnd; ++subIter) {
          if (subIter->_key == subClass)
            result = &subIter->_additionalWaitDeclarations;
          else
            result = subIter->findSubClassDependencies(subClass);
        };
        return result;  
      }
  };

  class MissingClassGeneration : public KeyInfo {
  private:
    translation_unit_decl _waitingClassDeclaration;
    std::vector<const clang::Decl*> _waitDeclarations;
    std::vector<MissingSubClassGeneration> _subGenerations;
    std::set<const clang::Decl*> _subWaitDeclarations;
    friend class VisitTable;

  public:
    MissingClassGeneration(const clang::RecordDecl* key,
        translation_unit_decl waitingDeclaration)
      : KeyInfo(key), _waitingClassDeclaration(waitingDeclaration) {}
    MissingClassGeneration(const MissingClassGeneration& source)
      : KeyInfo(source),
        _waitingClassDeclaration(source._waitingClassDeclaration)
      { const_cast<MissingClassGeneration&>(source)
            ._waitingClassDeclaration = NULL;
        _waitDeclarations.swap(const_cast<MissingClassGeneration&>(
            source)._waitDeclarations);
        _subGenerations.swap(const_cast<MissingClassGeneration&>(
            source)._subGenerations);
        _subWaitDeclarations.swap(const_cast<MissingClassGeneration&>(
            source)._subWaitDeclarations);
      }
    virtual ~MissingClassGeneration()
      { if (_waitingClassDeclaration) {
          free_translation_unit_decl(_waitingClassDeclaration);
          _waitingClassDeclaration = NULL;
        };
      }
    MissingSubClassGeneration& createSubDeclaration(
        const clang::RecordDecl* key, class_decl waitingSubClassDecl)
      { int position = 0;
        assert(_waitingClassDeclaration
          && _waitingClassDeclaration->tag_translation_unit_decl == COMPOUND
          && _waitingClassDeclaration->cons_translation_unit_decl.Compound
            .body->is_some);
        /* class_decl */ list parentList = (list) _waitingClassDeclaration
          ->cons_translation_unit_decl.Compound.body->content.container;
        while (parentList) {
          ++position;
          parentList = parentList->next;
        };
        _subGenerations.push_back(MissingSubClassGeneration(key,
            waitingSubClassDecl, position + _subGenerations.size()));
        return _subGenerations.back();
      }
    std::vector<const clang::Decl*>& waitDeclarations()
      { return _waitDeclarations; }
    const std::vector<const clang::Decl*>& waitDeclarations() const
      { return _waitDeclarations; }
    const std::set<const clang::Decl*>& subWaitDeclarations() const
      { return _subWaitDeclarations; }
    translation_unit_decl getWaitingClassDeclaration() const
      { return _waitingClassDeclaration; }
    const std::vector<const clang::Decl*>* findSubClassDependencies(
        const clang::Decl* subClass) const
      { const std::vector<const clang::Decl*>* result = NULL;
        std::vector<MissingSubClassGeneration>::const_iterator
          subIter = _subGenerations.begin(), subIterEnd = _subGenerations.end();
        for (; !result && subIter != subIterEnd; ++subIter) {
          if (subIter->key() == subClass)
            result = &subIter->waitDeclarations();
          else
            result = subIter->findSubClassDependencies(subClass);
        };
        return result;  
      }

    virtual bool isClassGenerationMissing() const { return true; }
    virtual bool isGenerationMissing() const { return true; }
    virtual bool isComplete() const
      { return !_waitingClassDeclaration && _waitDeclarations.empty()
          && _subGenerations.empty() && _subWaitDeclarations.empty();
      }
    virtual void print(std::ostream& out) const;
    virtual bool solve(const clang::Decl* decl, ForwardReferenceList& globals,
        VisitTable& table);
    virtual bool replaceWaitingBy(const clang::Decl* oldDecl,
        const std::vector<const clang::Decl*>& newDecls);
    void removeSubWait(const clang::Decl* decl);
    /* class_decl */ list& getContent() const
      { assert(_waitingClassDeclaration->tag_translation_unit_decl==COMPOUND);
        return *(/* class_decl */ list*) &_waitingClassDeclaration
          ->cons_translation_unit_decl.Compound.body->content.container;
      }
  };

  class InstanceClassGeneration : public MissingClassGeneration {
  public:
    typedef std::vector<KeyInfo*> WaitingDecls;

  private:
    WaitingDecls _waitingDecls;
    friend class VisitTable;

  public:
    InstanceClassGeneration(const clang::RecordDecl* key,
        translation_unit_decl waitingDeclaration)
      : MissingClassGeneration(key, waitingDeclaration) {}

    virtual void print(std::ostream& out) const { assert(false); }
    virtual bool isInstanceClass() const { return true; }
    virtual bool solve(const clang::Decl* decl, ForwardReferenceList& globals,
        VisitTable& table) { assert(false); return false; }
  };

  class MissingDecl : public KeyInfo {
  public:
    typedef std::vector<KeyInfo*> WaitingDecls;

  private:
    WaitingDecls _waitingDecls;
    friend class VisitTable;

  public:
    MissingDecl(const clang::Decl* decl) : KeyInfo(decl) {}
    virtual bool isMissingDecl() const { return true; }
    virtual bool isComplete() const { return false /* _waitingDecls.empty() */;}

    WaitingDecls& waitingDecls() { return _waitingDecls; }
    virtual void print(std::ostream& out) const;
  };

private:
  typedef std::set<KeyInfo*, KeyInfo::Less> ContentTable;
  typedef std::map<const clang::FunctionDecl*, std::list<bool*> >
    UpdateFunctionDeclarations;
 
  Clang_utils* _clangUtils;
  ContentTable _content;
  UpdateFunctionDeclarations _updateFunctionDeclarations;

protected:
  void solve(MissingSubClassGeneration& classDecl,
      MissingClassGeneration& rootDecl, ForwardReferenceList& globals);
  void addWaitFor(MissingSubClassGeneration& classDecl,
      class_decl classElement, MissingClassGeneration* parentDecl,
      ForwardReferenceList& globals, bool shouldBeSubkey=false);
  friend class MissingSubClassGeneration;
  friend class MissingClassGeneration;

  void enableNotificationFromBeforeReplaceWaiting(
      std::vector<const clang::Decl*>& dependencies,
      const std::vector<KeyInfo*>& waitingDecls, KeyInfo* originDependencies,
      bool mayHaveInstanceClass);

public:
  VisitTable() : _clangUtils(NULL) {}
  ~VisitTable()
    { ContentTable::iterator iterEnd = _content.end();
      for (ContentTable::iterator iter = _content.begin();
          iter != iterEnd; ++iter)
        if (*iter) delete *iter;
      _content.clear();
    }
  void setUtils(Clang_utils* clangUtils) { _clangUtils = clangUtils; }
  bool isComplete() const
    { ContentTable::iterator iterEnd = _content.end();
      for (ContentTable::iterator iter = _content.begin();
          iter != iterEnd; ++iter)
        if (!(*iter)->isComplete())
          return false;
      return true;
    }
  void printIncompleteDeclarations(std::ostream& out) const
    { ContentTable::iterator iterEnd = _content.end(), iter = _content.begin();
      while (iter != iterEnd) {
        if (!(*iter)->isComplete()) {
          (*iter)->print(out);
          out << '\n';
        };
        ++iter;
      };
    }
  void addDeclaration(const clang::Decl* decl, ForwardReferenceList& globals);
  void addFunctionDeclaration(const clang::FunctionDecl* decl,
    ForwardReferenceList& globals);
  void addSubDeclaration(const clang::Decl* decl, const clang::Decl* root,
      MissingSubClassGeneration* lastInstance /* should be a stack */,
      ForwardReferenceList& globals);

  bool hasVisited(const clang::Decl* decl,
      std::vector<const clang::Decl*>* alternativeDecls = NULL) const
    { KeyInfo locateKey(decl);
      ContentTable::const_iterator found = _content.find(&locateKey);
      bool result = false;
      if (found != _content.end()) {
         if (!(*found)->isMissingDecl()) {
           if (alternativeDecls && (*found)->isSubKey()
               && !((const SubKeyInfo&) **found).getSpecificWaitDeclarations()
                  .empty())
             *alternativeDecls = ((const SubKeyInfo&) **found)
               .getSpecificWaitDeclarations();
           else
             result = true;
         }
      };
      return result;
    }
  bool hasGenerated(const clang::Decl* decl) const
    { KeyInfo locateKey(decl);
      ContentTable::const_iterator found = _content.find(&locateKey);
      return (found != _content.end()) && !(*found)->isMissingDecl()
          && !(*found)->isGenerationMissing();
    }
  void ensureGeneration(const clang::Decl* decl,
      std::vector<const clang::Decl*>& waitedDeclarations) const;
  translation_unit_decl globalizeDecl(const clang::NamedDecl* decl,
      class_decl classElement) const;
  MissingClassGeneration& addInstanceClass(const clang::RecordDecl* decl,
      translation_unit_decl classDecl);
  MissingSubClassGeneration& addSubClass(MissingClassGeneration& firstInstance,
      MissingSubClassGeneration* lastClass, const clang::RecordDecl* decl,
      class_decl classDecl)
    { VisitTable::MissingSubClassGeneration* result;
      if (!lastClass)
        result = &firstInstance.createSubDeclaration(decl, classDecl);
      else
        result = &lastClass->createSubDeclaration(decl, classDecl);
      return *result;
    }
  void setInstanceClassAsComplete(InstanceClassGeneration* instance,
    ForwardReferenceList& globals);
  void makeTemporaryUnvisited(const clang::RecordDecl* decl)
    { KeyInfo locateKey(decl);
      ContentTable::iterator found = _content.find(&locateKey);
      assert(found != _content.end() && (*found)->isComplete()
          && !(*found)->isMissingDecl() && !(*found)->isGenerationMissing());
      _content.erase(found);
      _content.insert(new MissingDecl(decl)); // MissingClassGeneration(decl, NULL)
    }
  void makeTemporaryVisited(const clang::RecordDecl* decl,
      ForwardReferenceList& globals)
    { addDeclaration(decl, globals); }

  MissingClassGeneration& addIncompleteClass(const clang::RecordDecl* decl,
      std::vector<const clang::Decl*>& waitDeclarations,
      translation_unit_decl classDecl);

  MissingFunctionGeneration& addIncompleteFunction(
      const clang::FunctionDecl* decl,
      std::vector<const clang::Decl*>& waitDeclarations,
      translation_unit_decl functionDecl,
      translation_unit_decl functionBareDecl = NULL/* may be NULL */);

  void addUpdateFunction(const clang::FunctionDecl* decl,
      bool* furtherDefinitionFlag)
  { const clang::FunctionDecl* can = decl->getCanonicalDecl();
    UpdateFunctionDeclarations::iterator found
      = _updateFunctionDeclarations.find(can);
    if (found == _updateFunctionDeclarations.end()) {
      std::list<bool*> updates;
      updates.push_back(furtherDefinitionFlag);
      _updateFunctionDeclarations.insert(std::make_pair(can, updates));
    }
    else {
      if (found->second.empty()) // we have seen a declaration with a contract.
        *furtherDefinitionFlag = true;
      else { 
        if (*found->second.front()) 
          // we have seen a declaration with a contract.
          *furtherDefinitionFlag = true;
        found->second.push_back(furtherDefinitionFlag);
      }
    };
  }

  void visitFunctionDefinitionWithContract(const clang::FunctionDecl* decl)
    { 
      const clang::FunctionDecl* can = decl->getCanonicalDecl();
      UpdateFunctionDeclarations::iterator found
        = _updateFunctionDeclarations.find(can);
      if (found == _updateFunctionDeclarations.end())
        _updateFunctionDeclarations.insert(
          std::make_pair(can, std::list<bool*>()));
      else {
        //assert(!found->second.empty());
        std::list<bool*>::iterator iterEnd = found->second.end();
        for (std::list<bool*>::iterator iter = found->second.begin();
            iter != iterEnd; ++iter)
          **iter = true;
        found->second.clear();
      };
    }
};

#endif // Visit_TableH
