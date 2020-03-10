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
//   Implementation of VisitTable
//

#include "VisitTable.h"

void
VisitTable::MissingSubClassGeneration::print(std::ostream& out, bool ident)
      const {
  out << std::endl;
  for (int i = 0; i < ident; ++i)
    out << "  ";
  const clang::NamedDecl* decl = llvm::dyn_cast<clang::NamedDecl>
      (_key);
  if (decl)
    out << decl->getNameAsString() << ": ";
  else
    out << "clang_unnamed: ";
  if (_waitingSubClassDecl) {
    assert(_waitingSubClassDecl->tag_class_decl == CCOMPOUND);
    out << "non-generated subclass " << _waitingSubClassDecl
      ->cons_class_decl.CCompound.name << ": ";
  };
  if (!_additionalWaitDeclarations.empty()) {
    out << "waiting for ";
    std::vector<const clang::Decl*>::const_iterator
      iterEnd = _additionalWaitDeclarations.end(),
      iter = _additionalWaitDeclarations.begin();
    while (iter != iterEnd) {
      const clang::NamedDecl* decl = llvm::dyn_cast<clang::NamedDecl>
          (*iter);
      if (decl)
        out << decl->getNameAsString();
      else
        out << "clang_unnamed";
      ++iter;
      if (iter != iterEnd)
        out << ", ";
    };
  };
  if (!_subGenerations.empty()) {
    std::vector<MissingSubClassGeneration>::const_iterator
      iterEnd = _subGenerations.end(), iter = _subGenerations.begin();
    for (; iter != iterEnd; ++iter) {
      out << '\n';
      iter->print(out, ident+1);
    };
  };
}

bool
VisitTable::MissingSubClassGeneration::removeWait(const clang::Decl* decl) {
  std::vector<const clang::Decl*>::iterator
      iterEnd = _additionalWaitDeclarations.end();
  class_decl* parentDecl = &_waitingSubClassDecl;
  /* class_decl */ list* parentDeclList = NULL;
  int parentDeclPosition = 0;
  for (std::vector<const clang::Decl*>::iterator iter
      = _additionalWaitDeclarations.begin(); iter != iterEnd; ++iter) {
    if (*iter == decl) {
      _additionalWaitDeclarations.erase(iter);
      if (_additionalWaitDeclarations.empty()) {
        _waitingSubClassDecl = NULL;
        return _subGenerations.empty();
      };
      return false;
    };
  };
  std::set<const clang::Decl*>::iterator found
      = _subWaitDeclarations.find(decl);
  if (found != _subWaitDeclarations.end()) {
    std::vector<MissingSubClassGeneration>::iterator subIterEnd
        = _subGenerations.end();
    int subIndex = 0;
    for (std::vector<MissingSubClassGeneration>::iterator subIter
        = _subGenerations.begin(); subIter != subIterEnd; ) {
      if (subIter->removeWaitWithinClass(decl, parentDeclList,
          (/* class_decl */ list*)
            &(*parentDecl)->cons_class_decl.CCompound.body->content.container,
          parentDeclPosition, subIter->_parentPosition - subIndex)) {
        _subGenerations.erase(subIter);
        if (_subGenerations.empty()) {
          assert(_subWaitDeclarations.size() == 1);
          _subWaitDeclarations.clear();
          return _additionalWaitDeclarations.empty();
        };
        subIterEnd = _subGenerations.end();
      }
      else
        ++subIter;
      ++subIndex;
    }
    _subWaitDeclarations.erase(found);
  };
  return false;
}

bool
VisitTable::MissingSubClassGeneration::replaceWaitingBy(
    const clang::Decl* oldDecl, const std::vector<const clang::Decl*>& newDecls)
{ bool hasFoundInMain = false;
  { std::vector<const clang::Decl*>::iterator iterEnd
      = _additionalWaitDeclarations.end();
    std::vector<const clang::Decl*>::iterator
      iter = _additionalWaitDeclarations.begin();
    for (; !hasFoundInMain && iter != iterEnd; ++iter)
      hasFoundInMain = (*iter) == oldDecl;
    if (hasFoundInMain)
      _additionalWaitDeclarations.erase(iter);
  };
  if (hasFoundInMain) {
    int targetSize = _additionalWaitDeclarations.size();
    std::vector<const clang::Decl*>::const_iterator sourceIterEnd
        = newDecls.end();
    for (std::vector<const clang::Decl*>::const_iterator sourceIter
        = newDecls.begin(); sourceIter != sourceIterEnd; ++sourceIter) {
      bool hasFound = false;
      for (int targetIndex = 0; !hasFound && targetIndex < targetSize; 
          ++targetIndex)
        hasFound = *sourceIter
            == _additionalWaitDeclarations[targetIndex];
      if (!hasFound)
        _additionalWaitDeclarations.push_back(*sourceIter);
    };
  }
  else {
    std::set<const clang::Decl*>::iterator found = _subWaitDeclarations
      .find(oldDecl);
    if (found != _subWaitDeclarations.end()) {
      _subWaitDeclarations.erase(found);
      std::vector<const clang::Decl*>::const_iterator sourceIterEnd
        = newDecls.end();
      for (std::vector<const clang::Decl*>::const_iterator sourceIter
          = newDecls.begin(); sourceIter != sourceIterEnd; ++sourceIter)
        _subWaitDeclarations.insert(*sourceIter);
      std::vector<MissingSubClassGeneration>::iterator
          subIterEnd = _subGenerations.end();
      for (std::vector<MissingSubClassGeneration>::iterator subIter
          = _subGenerations.begin(); subIter != subIterEnd; ++subIter)
        subIter->replaceWaitingBy(oldDecl, newDecls);
    };
  }
  return true;
}

#if 0

bool
VisitTable::MissingSubClassGeneration::solve(const clang::Decl* decl,
    MissingClassGeneration& parentDecl, ForwardReferenceList& globals,
    VisitTable& table) {
  assert(_waitingSubClassDecl);
  bool result = _additionalWaitDeclarations.size() == 1;
  if (result) {
    if (*_additionalWaitDeclarations.begin() == decl) {
      std::vector<MissingSubClassGeneration>::iterator subIterEnd
          = _subGenerations.end();
      std::vector<MissingSubClassGeneration>::iterator subIter
          = _subGenerations.begin();
      /* class_decl */ list* parentDeclList = NULL;
      int parentDeclPosition = 0;
      int subIndex = 0;
      while (subIter != subIterEnd && (!subIter->_waitingSubClassDecl
          || subIter->removeWaitWithinClass(decl, parentDeclList,
               (/* class_decl */ list*) &_waitingSubClassDecl->cons_class_decl
                 .CCompound.body->content.container,
               parentDeclPosition, subIter->_parentPosition - subIndex))) {
        table.solve(*subIter, parentDecl, globals);
        ++subIter; ++subIndex;
      };
      if (subIter != subIterEnd) {
        assert(_waitingSubClassDecl->tag_class_decl == CCOMPOUND
            && _waitingSubClassDecl->cons_class_decl.CCompound.body->is_some);
        /* class_decl */ list subList = _waitingSubClassDecl->cons_class_decl
            .CCompound.body->content.container;
        assert(subList);
        while (subList) {
          class_decl classElement = (class_decl) subList->element.container;
          bool isEqual = classElement == subIter->_waitingSubClassDecl;
          if (!isEqual)
            isEqual = classElement->tag_class_decl == CCOMPOUND
              && subIter->_waitingSubClassDecl->tag_class_decl == CCOMPOUND
              && !strcmp(classElement->cons_class_decl.CCompound.name,
                  subIter->_waitingSubClassDecl->cons_class_decl.CCompound.name)
              && tkind_equal(
                  classElement->cons_class_decl.CCompound.template_kind,
                  subIter->_waitingSubClassDecl->cons_class_decl
                    .CCompound.template_kind);
          if (isEqual) {
            table.addWaitFor(*subIter, subIter->_waitingSubClassDecl,
              &parentDecl, globals,
              classElement!=subIter->_waitingSubClassDecl /* shouldBeSubkey */);
            ++subIter; ++subIndex;
            while (subIter != subIterEnd && (!subIter->_waitingSubClassDecl
                || subIter->removeWaitWithinClass(decl, parentDeclList,
                     (/* class_decl */ list*) &_waitingSubClassDecl
                       ->cons_class_decl.CCompound.body->content.container,
                     parentDeclPosition, subIter->_parentPosition - subIndex)))
            { table.solve(*subIter, parentDecl, globals);
              ++subIter; ++subIndex;
            };
            if (subIter == subIterEnd)
              break;
          };
          subList = subList->next;
        };
        assert(subIter == subIterEnd);
      };

      globals.add(_waitingSubClassDecl);
      _waitingSubClassDecl = NULL;
      _subGenerations.clear();
      return true;
    };
  }
  else {
    std::vector<const clang::Decl*>::iterator iterEnd
        = _additionalWaitDeclarations.end();
    bool hasFound = false;
    for (std::vector<const clang::Decl*>::iterator
        iter = _additionalWaitDeclarations.begin(); iter != iterEnd; ++iter) {
      if (*iter == decl) {
        _additionalWaitDeclarations.erase(iter);
        hasFound = true;
        break;
      };
    };
    if (hasFound);
      return false;
  };

  class_decl* parentDecl = &_waitingSubClassDecl;
  /* class_decl */ list* parentDeclList = NULL;
  int parentDeclPosition = 0;
  std::set<const clang::Decl*>::iterator
    found = _subWaitDeclarations.find(decl);
  assert(found != _subWaitDeclarations.end());
  std::vector<MissingSubClassGeneration>::iterator
    subIterEnd = _subGenerations.end();
  int subIndex = 0;
  for (std::vector<MissingSubClassGeneration>::iterator
      subIter = _subGenerations.begin(); subIter != subIterEnd; ) {
    if (subIter->removeWaitWithinClass(decl, parentDeclList,
        (/* class_decl */ list*)
          &(*parentDecl)->cons_class_decl.CCompound.body->content.container,
        parentDeclPosition, subIter->_parentPosition - subIndex)) {
      _subGenerations.erase(subIter);
      if (_subGenerations.empty()) {
        assert(_subWaitDeclarations.size() == 1);
        _subWaitDeclarations.clear();
        return _additionalWaitDeclarations.empty();
      };
      subIterEnd = _subGenerations.end();
    }
    else
      ++subIter;
    ++subIndex;
  }
  _subWaitDeclarations.erase(found);
  return false;
}

#endif

void
VisitTable::MissingFunctionGeneration::print(std::ostream& out) const {
  if (_waitingFunDefinition) {
    assert(_waitingFunDefinition->tag_translation_unit_decl == FUNCTION);
    decl_or_impl_name name = _waitingFunDefinition
      ->cons_translation_unit_decl.Function.fun_name;
    if (name->tag_decl_or_impl_name == DECLARATION)
      out << "non-generated method " << name->cons_decl_or_impl_name
        .Declaration.name << ": ";
    else {
      out << "non-generated function ";
      /* qualification */ list prequalification = name
          ->cons_decl_or_impl_name.Implementation.name->prequalification;
      while (prequalification) {
        qualification qual = (qualification) prequalification->element
            .container;
        if (qual->tag_qualification == QNAMESPACE)
          out << qual->cons_qualification.QNamespace.name;
        else if (qual->tag_qualification == QSTRUCTORCLASS)
          out << qual->cons_qualification.QStructOrClass.name;
        else {
           assert(qual->tag_qualification == QTEMPLATEINSTANCE);
           out << qual->cons_qualification.QTemplateInstance.name
               << "<...>";
        };
        out << "::";
        prequalification = prequalification->next;
      };
      out << name->cons_decl_or_impl_name.Implementation.name->decl_name;
      out << ": ";
    };
  }
  else {
    out << "non-generated function symbol ";
    KeyInfo::print(out);
  }
  if (!_waitDeclarations.empty()) {
    out << "waiting for ";
    std::vector<const clang::Decl*>::const_iterator
      iterEnd = _waitDeclarations.end(), iter = _waitDeclarations.begin();
    while (iter != iterEnd) {
      const clang::NamedDecl* decl = llvm::dyn_cast<clang::NamedDecl>
          (*iter);
      if (decl)
        out << decl->getNameAsString();
      else
        out << "clang_unnamed";
      ++iter;
      if (iter != iterEnd)
        out << ", ";
    };
  };
}

bool
VisitTable::MissingFunctionGeneration::solve(const clang::Decl* decl,
    ForwardReferenceList& globals, VisitTable& table)
{ assert(_waitingFunDefinition);
  bool result = _waitDeclarations.size() == 1;
  if (result) {
    assert(*_waitDeclarations.begin() == decl);
    globals.insertContainer(_waitingFunDefinition);
    if (_waitingAdditionalFunDefinition) {
      globals.insertContainer(_waitingAdditionalFunDefinition);
      _waitingAdditionalFunDefinition = NULL;
    };
    _waitDeclarations.clear();
    _waitingFunDefinition = NULL;
    return result;
  }
  else {
    std::vector<const clang::Decl*>::iterator iterEnd = _waitDeclarations.end();
    bool hasFound = false;
    for (std::vector<const clang::Decl*>::iterator
        iter = _waitDeclarations.begin(); iter != iterEnd; ++iter) {
      if (*iter == decl) {
        _waitDeclarations.erase(iter);
        hasFound = true;
        break;
      };
    };
    assert(hasFound);
  };
  return result;
}

bool
VisitTable::MissingFunctionGeneration::replaceWaitingBy(
    const clang::Decl* oldDecl, const std::vector<const clang::Decl*>& newDecls)
{ { std::vector<const clang::Decl*>::iterator iterEnd
      = _waitDeclarations.end();
    bool hasFound = false;
    std::vector<const clang::Decl*>::iterator
      iter = _waitDeclarations.begin();
    while (!hasFound && iter != iterEnd) {
      if ((hasFound = (*iter) == oldDecl) == false)
         ++iter;
    };
    assert(hasFound);
    _waitDeclarations.erase(iter);
  };
  int targetSize = _waitDeclarations.size();
  const clang::FunctionDecl* functionKey
      = llvm::dyn_cast<clang::FunctionDecl>(key());
  assert(functionKey);
  clang::Decl::Kind kindDecl = functionKey->getDeclContext()->getDeclKind();
  const clang::RecordDecl* parentDecl = 
    (kindDecl>=clang::Decl::firstRecord && kindDecl<=clang::Decl::lastRecord)
      ? static_cast<const clang::RecordDecl*>(functionKey->getDeclContext())
      : NULL;
  std::vector<const clang::Decl*>::const_iterator sourceIterEnd
      = newDecls.end();
  for (std::vector<const clang::Decl*>::const_iterator sourceIter
      = newDecls.begin(); sourceIter != sourceIterEnd; ++sourceIter) {
    if (functionKey && *sourceIter != parentDecl) {
      bool hasFound = false;
      for (int targetIndex = 0; !hasFound && targetIndex < targetSize; 
          ++targetIndex)
        hasFound = *sourceIter == _waitDeclarations[targetIndex];
      if (!hasFound)
        _waitDeclarations.push_back(*sourceIter);
    };
  };
  return _waitDeclarations.size() > 0;
}

void
VisitTable::MissingClassGeneration::print(std::ostream& out) const {
  if (_waitingClassDeclaration) {
    assert(_waitingClassDeclaration->tag_translation_unit_decl==COMPOUND);
    decl_or_impl_name name = _waitingClassDeclaration
      ->cons_translation_unit_decl.Compound.name;
    if (name->tag_decl_or_impl_name == DECLARATION)
      out << "non-generated class " << name->cons_decl_or_impl_name
        .Declaration.name << ": ";
    else {
      out << "non-generated extern class ";
      /* qualification */ list prequalification = name
          ->cons_decl_or_impl_name.Implementation.name->prequalification;
      while (prequalification) {
        qualification qual = (qualification) prequalification->element
            .container;
        if (qual->tag_qualification == QNAMESPACE)
          out << qual->cons_qualification.QNamespace.name;
        else if (qual->tag_qualification == QSTRUCTORCLASS)
          out << qual->cons_qualification.QStructOrClass.name;
        else {
           assert(qual->tag_qualification == QTEMPLATEINSTANCE);
           out << qual->cons_qualification.QTemplateInstance.name
               << "<...>";
        };
        out << "::";
        prequalification = prequalification->next;
      };
      out << name->cons_decl_or_impl_name.Implementation.name->decl_name;
      out << ": ";
    };
  }
  else {
    out << "non-generated class symbol ";
    KeyInfo::print(out);
  };
  if (!_waitDeclarations.empty()) {
    out << "waiting for ";
    std::vector<const clang::Decl*>::const_iterator
      iterEnd = _waitDeclarations.end(), iter = _waitDeclarations.begin();
    while (iter != iterEnd) {
      const clang::NamedDecl* decl = llvm::dyn_cast<clang::NamedDecl>
          (*iter);
      if (decl)
        out << decl->getNameAsString();
      else
        out << "clang_unnamed";
      ++iter;
      if (iter != iterEnd)
        out << ", ";
    };
  };
  if (!_subGenerations.empty()) {
    std::vector<MissingSubClassGeneration>::const_iterator
      iterEnd = _subGenerations.end(), iter = _subGenerations.begin();
    for (; iter != iterEnd; ++iter) {
      out << '\n';
      iter->print(out, 1);
    };
  };
}

bool
VisitTable::MissingClassGeneration::solve(const clang::Decl* decl,
    ForwardReferenceList& globals, VisitTable& table)
{ assert(_waitingClassDeclaration);
  bool result = _waitDeclarations.size() == 1;
  if (result) {
    if (*_waitDeclarations.begin() == decl) {
      globals.insertContainer(_waitingClassDeclaration);

      std::vector<MissingSubClassGeneration>::iterator subIterEnd
          = _subGenerations.end();
      std::vector<MissingSubClassGeneration>::iterator subIter
          = _subGenerations.begin();
      /* class_decl */ list* parentDeclList = NULL;
      int parentDeclPosition = 0;
      int subIndex = 0;
      assert(_subGenerations.empty()
        || (_waitingClassDeclaration->tag_translation_unit_decl == COMPOUND
          && _waitingClassDeclaration->cons_translation_unit_decl
              .Compound.body->is_some));
      while (subIter != subIterEnd && (!subIter->_waitingSubClassDecl
          || subIter->removeWaitWithinClass(decl, parentDeclList,
               (/* class_decl */ list*) &_waitingClassDeclaration
                 ->cons_translation_unit_decl.Compound.body->content.container,
               parentDeclPosition, subIter->_parentPosition - subIndex))) {
        table.solve(*subIter, *this, globals);
        ++subIter; ++subIndex;
      };
      if (subIter != subIterEnd) {
        // [TODO] use parentDeclList and subIter->_parentPosition
        //   instead of a new list.
        /* class_decl */ list subList = (list) _waitingClassDeclaration
            ->cons_translation_unit_decl.Compound.body->content.container;
        assert(subList);
        while (subList) {
          class_decl classElement = (class_decl) subList->element.container;
          bool isEqual = classElement == subIter->_waitingSubClassDecl;
          if (!isEqual)
            isEqual = classElement->tag_class_decl == CCOMPOUND
              && subIter->_waitingSubClassDecl->tag_class_decl == CCOMPOUND
              && !strcmp(classElement->cons_class_decl.CCompound.name,
                  subIter->_waitingSubClassDecl->cons_class_decl.CCompound.name)
              && tkind_equal(
                  classElement->cons_class_decl.CCompound.template_kind,
                  subIter->_waitingSubClassDecl->cons_class_decl
                    .CCompound.template_kind);
          if (isEqual) {
            table.addWaitFor(*subIter, subIter->_waitingSubClassDecl, this,
              globals, classElement!=subIter->_waitingSubClassDecl
              /* shouldBeSubkey */);
            ++subIter; ++subIndex;
            while (subIter != subIterEnd && (!subIter->_waitingSubClassDecl
                || subIter->removeWaitWithinClass(decl, parentDeclList,
                     (/* class_decl */ list*) &_waitingClassDeclaration
                       ->cons_translation_unit_decl.Compound
                         .body->content.container, parentDeclPosition,
                     subIter->_parentPosition - subIndex))) {
              table.solve(*subIter, *this, globals);
              ++subIter; ++subIndex;
            };
            if (subIter == subIterEnd)
              break;
          };
          subList = subList->next;
        };
        assert(subIter == subIterEnd);
      };

      _waitingClassDeclaration = NULL;
      _subGenerations.clear();
      return true;
    };
  }
  else {
    std::vector<const clang::Decl*>::iterator iterEnd = _waitDeclarations.end();
    bool hasFound = false;
    for (std::vector<const clang::Decl*>::iterator
        iter = _waitDeclarations.begin(); iter != iterEnd; ++iter) {
      if (*iter == decl) {
        _waitDeclarations.erase(iter);
        hasFound = true;
        break;
      };
    };
    if (hasFound)
      return false;
  };

  translation_unit_decl* parentDecl = &_waitingClassDeclaration;
  /* class_decl */ list* parentDeclList = NULL;
  int parentDeclPosition = 0;
  std::set<const clang::Decl*>::iterator
    found = _subWaitDeclarations.find(decl);
  assert(found != _subWaitDeclarations.end());
  std::vector<MissingSubClassGeneration>::iterator
    subIterEnd = _subGenerations.end();
  int subIndex = 0;
  for (std::vector<MissingSubClassGeneration>::iterator
      subIter = _subGenerations.begin(); subIter != subIterEnd; ) {
    if (subIter->removeWaitWithinClass(decl, parentDeclList,
        (/* class_decl */ list*) &(*parentDecl)
          ->cons_translation_unit_decl.Compound.body->content.container,
        parentDeclPosition, subIter->_parentPosition - subIndex)) {
      _subGenerations.erase(subIter);
      if (_subGenerations.empty()) {
        assert(_subWaitDeclarations.size() == 1);
        _subWaitDeclarations.clear();
        return _waitDeclarations.empty();
      };
      subIterEnd = _subGenerations.end();
    }
    else
      ++subIter;
    ++subIndex;
  }
  _subWaitDeclarations.erase(found);
  return false;
}

void
VisitTable::MissingClassGeneration::removeSubWait(const clang::Decl* decl) {
  std::set<const clang::Decl*>::iterator
    found = _subWaitDeclarations.find(decl);
  if (found != _subWaitDeclarations.end()) {
    /* class_decl */ list* parentDeclList = NULL;
    int parentDeclPosition = 0;
    std::vector<MissingSubClassGeneration>::iterator
      subIterEnd = _subGenerations.end();
    int subIndex = 0;
    for (std::vector<MissingSubClassGeneration>::iterator
        subIter = _subGenerations.begin(); subIter != subIterEnd; ) {
      if (!subIter->_waitingSubClassDecl ||
        subIter->removeWaitWithinClass(decl, parentDeclList,
          (/* class_decl */ list*) &_waitingClassDeclaration
            ->cons_translation_unit_decl.Compound.body->content.container,
          parentDeclPosition, subIter->_parentPosition - subIndex)) {
        _subGenerations.erase(subIter);
        if (_subGenerations.empty()) {
          assert(_subWaitDeclarations.size() == 1);
          _subWaitDeclarations.clear();
          return;
        };
        subIterEnd = _subGenerations.end();
      }
      else
        ++subIter;
      ++subIndex;
    }
    _subWaitDeclarations.erase(found);
  };
}

bool
VisitTable::MissingClassGeneration::replaceWaitingBy(const clang::Decl* oldDecl,
    const std::vector<const clang::Decl*>& newDecls) {
  bool hasFoundInMain = false;
  { std::vector<const clang::Decl*>::iterator
      iterEnd = _waitDeclarations.end(), iter = _waitDeclarations.begin();
    while(!hasFoundInMain && iter != iterEnd)
      if ((hasFoundInMain = (*iter) == oldDecl) == false)
        ++iter;
    if (hasFoundInMain)
      _waitDeclarations.erase(iter);
  };
  if (hasFoundInMain) {
    int targetSize = _waitDeclarations.size();
    std::vector<const clang::Decl*>::const_iterator sourceIterEnd
        = newDecls.end();
    for (std::vector<const clang::Decl*>::const_iterator sourceIter
        = newDecls.begin(); sourceIter != sourceIterEnd; ++sourceIter) {
      bool hasFound = false;
      for (int targetIndex = 0; !hasFound && targetIndex < targetSize; 
          ++targetIndex)
        hasFound = *sourceIter == _waitDeclarations[targetIndex];
      if (!hasFound)
        _waitDeclarations.push_back(*sourceIter);
    };
  }
  else {
    std::set<const clang::Decl*>::iterator found = _subWaitDeclarations
      .find(oldDecl);
    assert(found != _subWaitDeclarations.end());
    _subWaitDeclarations.erase(found);
    { std::vector<const clang::Decl*>::const_iterator sourceIterEnd
        = newDecls.end();
      for (std::vector<const clang::Decl*>::const_iterator sourceIter
          = newDecls.begin(); sourceIter != sourceIterEnd; ++sourceIter)
        _subWaitDeclarations.insert(*sourceIter);
    };
    std::vector<MissingSubClassGeneration>::iterator
        subIterEnd = _subGenerations.end();
    for (std::vector<MissingSubClassGeneration>::iterator subIter
        = _subGenerations.begin(); subIter != subIterEnd; ++subIter)
      subIter->replaceWaitingBy(oldDecl, newDecls);
  }
  return true;
}

void
VisitTable::MissingDecl::print(std::ostream& out) const {
  out << "missing declaration: ";
  KeyInfo::print(out);
  if (!_waitingDecls.empty()) {
    WaitingDecls::const_iterator iterEnd = _waitingDecls.end(),
      iter = _waitingDecls.begin();
    out << "expected by\n";
    while (iter != iterEnd) {
      out << "\t- ";
      (*iter)->print(out);
      ++iter;
      if (iter != iterEnd)
        out << '\n';
    };
  };
}

translation_unit_decl
VisitTable::globalizeDecl(const clang::NamedDecl* decl,
    class_decl classElement) const {
  translation_unit_decl result;
  if (classElement->tag_class_decl == CMETHOD) {
    /* statement list */ option body;
    tkind templateParameters = classElement->cons_class_decl.CMethod
        .template_kind;
    classElement->cons_class_decl.CMethod.template_kind = tkind_TStandard();
    if (classElement->cons_class_decl.CMethod.body->is_some) {
      body = opt_some_container((list) classElement->cons_class_decl.CMethod
          .body->content.container);
      free(classElement->cons_class_decl.CMethod.body);
      classElement->cons_class_decl.CMethod.body = opt_none();
    }
    else
      body = opt_none();
    /* arg_decl */ list args = classElement->cons_class_decl.CMethod.args;
    classElement->cons_class_decl.CMethod.args = NULL;
    /* function_contract */ option spec = classElement->cons_class_decl
        .CMethod.fun_spec;
    classElement->cons_class_decl.CMethod.fun_spec = opt_none();

    result = translation_unit_decl_Function(
      decl_or_impl_name_Implementation(_clangUtils->makeQualifiedName(*decl)),
      funkind_dup(classElement->cons_class_decl.CMethod.kind),
      copy_loc(classElement->cons_class_decl.CMethod.loc),
      qual_type_dup(classElement->cons_class_decl.CMethod
        .return_type), args, body, false /* is_extern_c */,
      false /* ghost: TODO: refine that for ghost classes. */,
      classElement->cons_class_decl.CMethod.is_variadic, templateParameters,
       true /* has_further_definition */,
       opt_none() /* throws */,
       spec);
  }
  else if (classElement->tag_class_decl == CCOMPOUND) {
    /* class_decl list */ option body;
    tkind templateParameters = classElement->cons_class_decl.CCompound
        .template_kind;
    classElement->cons_class_decl.CCompound.template_kind = tkind_TStandard();
    if (classElement->cons_class_decl.CCompound.body->is_some) {
      body = opt_some_container((list) classElement->cons_class_decl.CCompound
          .body->content.container);
      free(classElement->cons_class_decl.CCompound.body);
      classElement->cons_class_decl.CCompound.body = opt_none();
    }
    else
      body = opt_none();
    /* inheritance list */ option inheritanceList
      = classElement->cons_class_decl.CCompound.inherits;
    classElement->cons_class_decl.CCompound.inherits = opt_none();
    result =
      translation_unit_decl_Compound(
        copy_loc(classElement->cons_class_decl.CCompound.loc),
        decl_or_impl_name_Implementation(_clangUtils->makeQualifiedName(*decl)),
        classElement->cons_class_decl.CCompound.kind, inheritanceList, body,
        classElement->cons_class_decl.CCompound.has_virtual,
        templateParameters, false /*is_extern_c_context*/, false /* ghost */);
  }
  else
    assert(false);
  free_class_decl(classElement);
  return result;
}

void
VisitTable::solve(MissingSubClassGeneration& classDecl,
    MissingClassGeneration& rootDecl,
    ForwardReferenceList& globals) {
  assert(!classDecl._waitingSubClassDecl
      && classDecl._additionalWaitDeclarations.empty());
  std::vector<MissingSubClassGeneration>::iterator subIterEnd
      = classDecl._subGenerations.end();
  std::vector<MissingSubClassGeneration>::iterator subIter
      = classDecl._subGenerations.begin();
  while (subIter != subIterEnd && !subIter->_waitingSubClassDecl) {
    solve(*subIter, rootDecl, globals);
    ++subIter;
  };
  if (subIter != subIterEnd) {
    assert(classDecl._waitingSubClassDecl->tag_class_decl == CCOMPOUND &&
      classDecl._waitingSubClassDecl->cons_class_decl.CCompound.body->is_some);
    /* class_decl */ list subList = (list) classDecl._waitingSubClassDecl
        ->cons_class_decl.CCompound.body->content.container;
    assert(subList);
    while (subList) {
      class_decl classElement = (class_decl) subList->element.container;
      bool isEqual = classElement == subIter->_waitingSubClassDecl;
      if (!isEqual)
        isEqual = classElement->tag_class_decl == CCOMPOUND
          && subIter->_waitingSubClassDecl->tag_class_decl == CCOMPOUND
          && !strcmp(classElement->cons_class_decl.CCompound.name,
              subIter->_waitingSubClassDecl->cons_class_decl.CCompound.name)
          && tkind_equal(
              classElement->cons_class_decl.CCompound.template_kind,
              subIter->_waitingSubClassDecl->cons_class_decl
                .CCompound.template_kind);
      if (isEqual) {
        addWaitFor(*subIter, subIter->_waitingSubClassDecl, &rootDecl,
          globals, classElement != subIter->_waitingSubClassDecl
          /* shouldBeSubkey */);
        ++subIter;
        while (subIter != subIterEnd && !subIter->_waitingSubClassDecl) {
          solve(*subIter, rootDecl, globals);
          ++subIter;
        };
        if (subIter == subIterEnd)
          break;
      };
      subList = subList->next;
    };
    assert(subIter == subIterEnd);
  };

  KeyInfo locateKey(classDecl._key);
  ContentTable::iterator found = _content.find(&locateKey);
  if (found != _content.end() && (*found)->isMissingDecl()) {
    MissingDecl* waitingForDecl = (MissingDecl*) *found;
    MissingDecl::WaitingDecls::iterator iterEnd
      = waitingForDecl->waitingDecls().end();
    for (MissingDecl::WaitingDecls::iterator iter
        = waitingForDecl->waitingDecls().begin(); iter != iterEnd; ++iter) {
      if ((*iter)->solve(classDecl._key, globals, *this)) {
        KeyInfo* toDelete = *iter;
        *iter = new KeyInfo(**iter);
        delete toDelete;
      };
    };
    KeyInfo* toDelete = waitingForDecl;
    _content.erase(found);
    _content.insert(new KeyInfo(classDecl._key));
    delete toDelete;
  };
}

void
VisitTable::addWaitFor(MissingSubClassGeneration& classDecl,
    class_decl classElement, MissingClassGeneration* parentDecl,
    ForwardReferenceList& globals, bool shouldBeSubkey)
{ assert(classDecl._waitingSubClassDecl
      && !classDecl._additionalWaitDeclarations.empty());
  KeyInfo* missingGeneration = NULL;
  std::vector<const clang::Decl*>* waitDeclarations = NULL;
  bool shouldPreempt = false;

  if (classElement->tag_class_decl == CMETHOD) {
    assert(classElement->cons_class_decl.CMethod.body->is_some);
    assert(!shouldBeSubkey);
    /* statement */ list body = (list) classElement->cons_class_decl.CMethod
        .body->content.container;
    free(classElement->cons_class_decl.CMethod.body);
    classElement->cons_class_decl.CMethod.body = opt_none();
    assert(llvm::dyn_cast<clang::NamedDecl>(classDecl._key));
    /* arg_decl */ list copyArgs = NULL;
    /* arg_decl */ list& endCopyArgs = copyArgs;
    /* arg_decl */ list iterArgs = classElement->cons_class_decl.CMethod.args;
    while (iterArgs) {
      endCopyArgs = cons_container(arg_decl_dup((arg_decl)
            iterArgs->element.container), NULL);
      endCopyArgs = endCopyArgs->next;
      iterArgs = iterArgs->next;
    };
    /* function_contract */ option spec = classElement->cons_class_decl
        .CMethod.fun_spec;
    classElement->cons_class_decl.CMethod.fun_spec = opt_none();

    assert(llvm::dyn_cast<clang::FunctionDecl>(classDecl._key));
    tkind templateParameters = tkind_dup(classElement->cons_class_decl.CMethod
        .template_kind);
    MissingFunctionGeneration* insertion = new MissingFunctionGeneration(
      static_cast<const clang::FunctionDecl*>(classDecl._key),
      translation_unit_decl_Function(
        decl_or_impl_name_Implementation(_clangUtils->makeQualifiedName(
          *static_cast<const clang::NamedDecl*>(classDecl._key))),
        funkind_dup(classElement->cons_class_decl.CMethod.kind),
        copy_loc(classElement->cons_class_decl.CMethod.loc),
        qual_type_dup(classElement->cons_class_decl.CMethod
          .return_type), copyArgs, opt_some_container(body), 
        false /* is_extern_c */,
        false /* ghost */,
        classElement->cons_class_decl.CMethod.is_variadic, templateParameters,
        false /* has_further_definition */,
        opt_none() /* throws */,
        spec));
    insertion->_waitDeclarations.swap(classDecl._additionalWaitDeclarations);
    missingGeneration = insertion;
    waitDeclarations = &insertion->_waitDeclarations;
  }
  else if (classElement->tag_class_decl == CCOMPOUND) {
    assert(classElement->cons_class_decl.CCompound.body->is_some);
    /* class_decl */ list body = (list) classElement->cons_class_decl.CCompound
        .body->content.container;
    free(classElement->cons_class_decl.CCompound.body);
    classElement->cons_class_decl.CCompound.body = opt_none();
    tkind templateParameters = classElement->cons_class_decl
        .CCompound.template_kind;
    classElement->cons_class_decl.CCompound.template_kind = tkind_TStandard();
    assert(llvm::dyn_cast<clang::NamedDecl>(classDecl._key));
    /* inheritance list */ option inheritanceList
      = classElement->cons_class_decl.CCompound.inherits;
    classElement->cons_class_decl.CCompound.inherits = opt_none();
    
    assert(llvm::dyn_cast<clang::RecordDecl>(classDecl._key));
    MissingClassGeneration* insertion = new MissingClassGeneration(
      static_cast<const clang::RecordDecl*>(classDecl._key),
      translation_unit_decl_Compound(
        copy_loc(classElement->cons_class_decl.CCompound.loc),
        decl_or_impl_name_Implementation(_clangUtils->makeQualifiedName(
          *static_cast<const clang::NamedDecl*>(classDecl._key))),
        classElement->cons_class_decl.CCompound.kind,
        inheritanceList, opt_some_container(body),
        classElement->cons_class_decl.CCompound.has_virtual,
        templateParameters, false /* is_extern_c_context */, false /*ghost*/));
    insertion->_waitDeclarations.swap(classDecl._additionalWaitDeclarations);
    insertion->_subGenerations.swap(classDecl._subGenerations);
    insertion->_subWaitDeclarations.swap(classDecl._subWaitDeclarations);
    missingGeneration = insertion;
    waitDeclarations = &insertion->_waitDeclarations;
    shouldPreempt = true;
  }
  else
    assert(false);

  assert(missingGeneration && waitDeclarations);
  KeyInfo locateKey(classDecl._key);
  ContentTable::iterator found = _content.lower_bound(&locateKey);
  if (found == _content.end() || KeyInfo::Less()(*found, &locateKey))
    found = _content.insert(found, missingGeneration);
  else {
    KeyInfo* toDelete;
    if (!shouldBeSubkey) {
      assert((*found)->isMissingDecl());
      MissingDecl* waitingForDecl = (MissingDecl*) *found;
      MissingDecl::WaitingDecls::iterator iterEnd
        = waitingForDecl->waitingDecls().end();
      for (MissingDecl::WaitingDecls::iterator iter
          = waitingForDecl->waitingDecls().begin(); iter != iterEnd; ++iter) {
        if ((*iter)->solve(classDecl._key, globals, *this)) {
          toDelete = *iter;
          *iter = new KeyInfo(**iter);
          delete toDelete;
        };
      };
      toDelete = waitingForDecl;
    }
    else {
      assert((*found)->isSubKey());
      toDelete = *found;
    }
    _content.erase(found);
    _content.insert(missingGeneration);
    delete toDelete;
  };

  // update the MissingDecl to enable solving notifications.
  std::vector<const clang::Decl*>::const_iterator endWaitIterEnd
    = waitDeclarations->end();
  for (std::vector<const clang::Decl*>::const_iterator endWaitIter
        = waitDeclarations->begin();
      endWaitIter != endWaitIterEnd; ++endWaitIter) {
    KeyInfo locateDecl(*endWaitIter);
    ContentTable::iterator found = _content.find(&locateDecl);
    if (found == _content.end()) {
      assert(shouldBeSubkey);
      MissingDecl* newMissing = new MissingDecl(*endWaitIter);
      _content.insert(newMissing);
      newMissing->waitingDecls().push_back(missingGeneration);
    }
    else if ((*found)->isMissingDecl()) {
      { std::vector<KeyInfo*>::iterator
           locateIter = ((MissingDecl&) **found).waitingDecls().begin(),
           locateIterEnd = ((MissingDecl&) **found).waitingDecls().end();
        bool hasFound = false;
        for (; !hasFound && locateIter != locateIterEnd; ++locateIter) {
          if (*locateIter == parentDecl) {
            hasFound = true;
            ((MissingDecl&) **found).waitingDecls().erase(locateIter);
          }
        };
      };
      // see enableNotificationFromBeforeReplaceWaiting that has not been
      //   called by MissingSubClassGeneration::setAsComplete
      if (!shouldPreempt)
        ((MissingDecl&) **found).waitingDecls().push_back(missingGeneration);
      else {
        std::vector<KeyInfo*>::iterator
           locateIter = ((MissingDecl&) **found).waitingDecls().begin(),
           locateIterEnd = ((MissingDecl&) **found).waitingDecls().end();
        // [TODO] may happen: function other subclass subclass
        //                    where function depends on subclass
        for (; locateIter != locateIterEnd; ++locateIter) {
          if ((*locateIter)->isFunctionGenerationMissing()
              && ((const clang::FunctionDecl*)
                     (*locateIter)->key())->getParent()
                == ((const clang::RecordDecl*)
                     missingGeneration->key())->getParent())
            break;
        }
        if (locateIter != locateIterEnd)
          ((MissingDecl&) **found).waitingDecls().insert(locateIter,
            missingGeneration);
        else
          ((MissingDecl&) **found).waitingDecls().push_back(missingGeneration);
      }
    }
    else if ((*found)->isInstanceClass()) {
      if (((InstanceClassGeneration*) *found)->_waitingDecls.empty()
          || ((InstanceClassGeneration*) *found)->_waitingDecls.back()
               !=missingGeneration) {
        { std::vector<KeyInfo*>::iterator locateIter
               = ((InstanceClassGeneration&) **found)._waitingDecls.begin(),
             locateIterEnd
               = ((InstanceClassGeneration&) **found)._waitingDecls.end();
          bool hasFound = false;
          for (; !hasFound && locateIter != locateIterEnd; ++locateIter) {
            if (*locateIter == parentDecl) {
              hasFound = true;
              ((InstanceClassGeneration&) **found)._waitingDecls
                .erase(locateIter);
            }
          };
        };
        ((InstanceClassGeneration*) *found)
          ->_waitingDecls.push_back(missingGeneration);
      };
    }
    else { // should not occur
      assert(false);
    }
  };
}

void
VisitTable::addDeclaration(const clang::Decl* decl,
    ForwardReferenceList& globals) {
  KeyInfo locateKey(decl);
  ContentTable::iterator found = _content.lower_bound(&locateKey);
  if (found != _content.end() && (*found)->_key == decl) {
    assert((*found)->isMissingDecl() || !(*found)->isGenerationMissing());
    if (!(*found)->isMissingDecl())
      return;
    MissingDecl* waitingForDecl = (MissingDecl*) *found;
    MissingDecl::WaitingDecls::iterator iterEnd
      = waitingForDecl->waitingDecls().end();
    KeyInfo* toDelete = waitingForDecl;
    _content.erase(found);
    for (MissingDecl::WaitingDecls::iterator iter = waitingForDecl
        ->waitingDecls().begin(); iter != iterEnd; ++iter) {
      if ((*iter)->solve(decl, globals, *this)) {
        KeyInfo* toLocalDelete = *iter;
        ContentTable::iterator localFound = _content.find(toLocalDelete);
        assert(localFound != _content.end() && *localFound == toLocalDelete);
        _content.erase(localFound);
        *iter = new KeyInfo(**iter);
        _content.insert(*iter);
        delete toLocalDelete;
      };
    };
    _content.insert(new KeyInfo(decl));
    delete toDelete;
  }
  else
    _content.insert(new KeyInfo(decl));
}

void
VisitTable::enableNotificationFromBeforeReplaceWaiting(
    std::vector<const clang::Decl*>& dependencies,
    const std::vector<KeyInfo*>& waitingDecls,
    KeyInfo* originDependencies, bool mayHaveInstanceClass) {
  std::vector<const clang::Decl*>::iterator
    absentIterEnd = dependencies.end();
  for (std::vector<const clang::Decl*>::iterator
      absentIter = dependencies.begin();
      absentIter != absentIterEnd; ++absentIter) {
    KeyInfo locateKey(*absentIter);
    ContentTable::const_iterator found = _content.find(&locateKey);
    if (found == _content.end()) {
      MissingDecl* newMissing = new MissingDecl(*absentIter);
      _content.insert(newMissing);
      if (originDependencies)
        newMissing->_waitingDecls.push_back(originDependencies);
      newMissing->_waitingDecls.insert(newMissing->_waitingDecls.end(),
        waitingDecls.begin(), waitingDecls.end());
    }
    else if ((*found)->isMissingDecl()) { // has locally been found after
      MissingDecl* newMissing = (MissingDecl*) *found;
      std::vector<KeyInfo*>::const_iterator
        iterSourceEnd = waitingDecls.end();
      int sizeTarget = newMissing->_waitingDecls.size();
      if (originDependencies)
        newMissing->_waitingDecls.push_back(originDependencies);
      for (std::vector<KeyInfo*>::const_iterator iterSource
            = waitingDecls.begin(); iterSource != iterSourceEnd; ++iterSource) {
        bool hasFound = false;
        int foundIndex = 0;
        for (int indexTarget = 0; !hasFound && indexTarget < sizeTarget;
            ++indexTarget) {
          if (*iterSource == newMissing->_waitingDecls[indexTarget]) {
            hasFound = true;
            foundIndex = indexTarget;
          }
        };
        if (hasFound) { // the method soon depends from newMissing
          // but the generation of the method should occur after the class!
          newMissing->_waitingDecls.erase(
            newMissing->_waitingDecls.begin() + foundIndex);
        }
        newMissing->_waitingDecls.push_back(*iterSource);
      };
    }
    else if (mayHaveInstanceClass && (*found)->isInstanceClass()) {
      InstanceClassGeneration* newMissing = (InstanceClassGeneration*) *found;
      std::vector<KeyInfo*>::const_iterator
        iterSourceEnd = waitingDecls.end();
      int sizeTarget = newMissing->_waitingDecls.size();
      if (originDependencies)
        newMissing->_waitingDecls.push_back(originDependencies);
      for (std::vector<KeyInfo*>::const_iterator iterSource
            = waitingDecls.begin(); iterSource != iterSourceEnd; ++iterSource) {
        bool hasFound = false;
        int foundIndex = 0;
        for (int indexTarget = 0; !hasFound && indexTarget < sizeTarget;
            ++indexTarget) {
          if (*iterSource == newMissing->_waitingDecls[indexTarget]) {
            hasFound = true;
            foundIndex = indexTarget;
          }
        };
        if (hasFound) { // the method soon depends from newMissing
          // but the generation of the method should occur after the class!
          newMissing->_waitingDecls.erase(
            newMissing->_waitingDecls.begin() + foundIndex);
        }
        newMissing->_waitingDecls.push_back(*iterSource);
      };
    }
    else { // should not occur
       int index = absentIter - dependencies.begin();
       dependencies.erase(absentIter);
       absentIter =  dependencies.begin() + index - 1;
       absentIterEnd =  dependencies.end();
    };
  }
}

void
VisitTable::addFunctionDeclaration(const clang::FunctionDecl* decl,
    ForwardReferenceList& globals) {
  clang::Decl::Kind parentKind = decl->getDeclContext()->getDeclKind();
  std::vector<const clang::Decl*> parentDependencies;
  if (parentKind >= clang::Decl::firstRecord
      && parentKind <= clang::Decl::lastRecord)
    ensureGeneration(static_cast<const clang::RecordDecl*>
        (decl->getDeclContext()), parentDependencies);

  KeyInfo locateKey(decl);
  ContentTable::iterator found = _content.lower_bound(&locateKey);
  if (found != _content.end() && (*found)->_key == decl) {
    assert((*found)->isMissingDecl() || !(*found)->isGenerationMissing());
    if (!(*found)->isMissingDecl())
      return;
    MissingDecl* waitingForDecl = (MissingDecl*) *found;
    if (!parentDependencies.empty())
      enableNotificationFromBeforeReplaceWaiting(parentDependencies,
          waitingForDecl->_waitingDecls, NULL /* originDependencies */,
          true /* mayHaveInstanceClass */);

    MissingDecl::WaitingDecls::iterator iterEnd
      = waitingForDecl->waitingDecls().end();
    KeyInfo* toDelete = waitingForDecl;
    _content.erase(found);
    for (MissingDecl::WaitingDecls::iterator iter = waitingForDecl
        ->waitingDecls().begin(); iter != iterEnd; ++iter) {
      bool doesSolve = true;
      if (!parentDependencies.empty())
        doesSolve = !(*iter)->replaceWaitingBy(decl, parentDependencies);
      if (doesSolve) {
        if ((*iter)->solve(decl, globals, *this)) {
          KeyInfo* toLocalDelete = *iter;
          ContentTable::iterator localFound = _content.find(toLocalDelete);
          assert(localFound != _content.end() && *localFound == toLocalDelete);
          _content.erase(localFound);
          *iter = new KeyInfo(**iter);
          _content.insert(*iter);
          delete toLocalDelete;
        };
      }
    };
    _content.insert(new KeyInfo(decl));
    delete toDelete;
  }
  else
    _content.insert(new KeyInfo(decl));
}

void
VisitTable::addSubDeclaration(const clang::Decl* decl,
    const clang::Decl* root,
    MissingSubClassGeneration* lastInstance /* should be a stack */,
    ForwardReferenceList& globals) {
  KeyInfo locateKey(decl);
  ContentTable::iterator found = _content.lower_bound(&locateKey);
  if (found != _content.end() && (*found)->_key == decl) {
    assert((*found)->isMissingDecl() || !(*found)->isGenerationMissing());
    if (!(*found)->isMissingDecl())
      return;
    MissingDecl* waitingForDecl = (MissingDecl*) *found;
    MissingDecl::WaitingDecls::iterator iterEnd
      = waitingForDecl->waitingDecls().end();
    KeyInfo* toDelete = waitingForDecl;
    _content.erase(found);
    for (MissingDecl::WaitingDecls::iterator iter = waitingForDecl
        ->waitingDecls().begin(); iter != iterEnd; ++iter) {
      if ((*iter)->solve(decl, globals, *this)) {
        KeyInfo* toLocalDelete = *iter;
        ContentTable::iterator localFound = _content.find(toLocalDelete);
        assert(localFound != _content.end() && *localFound == toLocalDelete);
        _content.erase(localFound);
        *iter = new KeyInfo(**iter);
        _content.insert(*iter);
        delete toLocalDelete;
      };
    };
    delete toDelete;
  };
  SubKeyInfo* subInfo = new SubKeyInfo(decl, root);
  _content.insert(subInfo);
  if (subInfo && lastInstance)
    subInfo->addSpecificWaitDeclarations(lastInstance->waitDeclarations());
}

void
VisitTable::ensureGeneration(const clang::Decl* decl,
    std::vector<const clang::Decl*>& waitedDeclarations) const
{ KeyInfo locateKey(decl);
  ContentTable::const_iterator found = _content.find(&locateKey);
  const clang::Decl* declToInsert = NULL;
  const std::vector<const clang::Decl*>* declsToInsert = NULL;
  const std::vector<const clang::Decl*>* additionalDeclsToInsert = NULL;
  const std::vector<const clang::Decl*>* specificAdditionalDeclsToInsert = NULL;
  if (found == _content.end())
    declToInsert = decl;
  else {
    if ((*found)->isSubKey()) {
      specificAdditionalDeclsToInsert =
        &static_cast<const SubKeyInfo*>(*found)->getSpecificWaitDeclarations();
      KeyInfo locateRootKey(static_cast<const SubKeyInfo*>(*found)->root());
      found = _content.find(&locateRootKey);
      assert(found != _content.end());
      if ((*found)->isClassGenerationMissing())
        additionalDeclsToInsert = ((const MissingClassGeneration*) *found)
          ->findSubClassDependencies(decl);
      decl = locateRootKey.key();
    };
    if ((*found)->isMissingDecl())
      declToInsert = decl;
    else if ((*found)->isGenerationMissing()) {
      if ((*found)->isInstanceClass())
        declToInsert = decl;
      else if ((*found)->isFunctionGenerationMissing()) {
        const MissingFunctionGeneration* functionInfo
            = (const MissingFunctionGeneration*) *found;
        declsToInsert = &functionInfo->waitDeclarations();
      }
      else {
        assert((*found)->isClassGenerationMissing());
        const MissingClassGeneration* classInfo
            = (const MissingClassGeneration*) *found;
        declsToInsert = &classInfo->waitDeclarations();
      };
    };
  };

  if (declToInsert) {
    bool hasFound = false;
    std::vector<const clang::Decl*>::const_iterator
      iterEnd = waitedDeclarations.end(), iter = waitedDeclarations.begin();
    for (; !hasFound && iter != iterEnd; ++iter)
      hasFound = *iter == declToInsert;
    if (!hasFound)
      waitedDeclarations.push_back(declToInsert);
  };
  while (declsToInsert
         || additionalDeclsToInsert || specificAdditionalDeclsToInsert) {
    if (declsToInsert) {
      std::vector<const clang::Decl*>::const_iterator
        sourceIterEnd = declsToInsert->end(),
        sourceIter = declsToInsert->begin();
      for (; sourceIter != sourceIterEnd; ++sourceIter) {
        declToInsert = *sourceIter;
        bool hasFound = false;
        std::vector<const clang::Decl*>::const_iterator
          iterEnd = waitedDeclarations.end(), iter = waitedDeclarations.begin();
        for (; !hasFound && iter != iterEnd; ++iter)
          hasFound = *iter == declToInsert;
        if (!hasFound)
          waitedDeclarations.push_back(declToInsert);
      }
    };
    if (additionalDeclsToInsert) {
      declsToInsert = additionalDeclsToInsert;
      additionalDeclsToInsert = NULL;
    }
    else if (specificAdditionalDeclsToInsert) {
      declsToInsert = specificAdditionalDeclsToInsert;
      specificAdditionalDeclsToInsert = NULL;
    }
    else
      declsToInsert = NULL;
  };
}

VisitTable::MissingClassGeneration&
VisitTable::addInstanceClass(const clang::RecordDecl* decl,
    translation_unit_decl classDecl) {
  KeyInfo locateKey(decl);
  ContentTable::iterator found = _content.lower_bound(&locateKey);
  InstanceClassGeneration* result;
  if (found != _content.end() && (*found)->_key == decl) {
    assert((*found)->isMissingDecl());
    MissingDecl* oldMissing = (MissingDecl*) *found;
    result = new InstanceClassGeneration(decl, classDecl);
    _content.erase(found);
    _content.insert(result);
    result->_waitingDecls.swap(oldMissing->_waitingDecls);
    delete oldMissing;
  }
  else {
    result = new InstanceClassGeneration(decl, classDecl);
    _content.insert(found, result);
  };
  return *result;
}

void
VisitTable::setInstanceClassAsComplete(InstanceClassGeneration* instance,
    ForwardReferenceList& globals) {
  if (!instance->_subGenerations.empty()) {
    std::vector<MissingSubClassGeneration>::const_iterator
      subIterEnd = instance->_subGenerations.end(),
      subIter = instance->_subGenerations.begin();
    for (; subIter != subIterEnd; ++subIter) {
      instance->_subWaitDeclarations.insert(
        subIter->_additionalWaitDeclarations.begin(),
        subIter->_additionalWaitDeclarations.end());
      instance->_subWaitDeclarations.insert(
        subIter->_subWaitDeclarations.begin(),
        subIter->_subWaitDeclarations.end());
    };
  };
  int absentSize = instance->_waitDeclarations.size();
  for (int absentIndex = absentSize-1; absentIndex >= 0; --absentIndex) {
    const clang::Decl* decl = instance->_waitDeclarations[absentIndex];
    if (decl == instance->key()) {
      instance->_waitDeclarations.erase(instance->_waitDeclarations.begin()
          + absentIndex);
      instance->removeSubWait(decl);
    }
    else {
      KeyInfo locateKey(decl);
      ContentTable::const_iterator found = _content.find(&locateKey);
      if (found != _content.end() && !(*found)->isMissingDecl()) {
        if ((*found)->isGenerationMissing())
          assert(!(*found)->isInstanceClass());
        else {
          instance->_waitDeclarations.erase(
              instance->_waitDeclarations.begin() + absentIndex);
          instance->removeSubWait(decl);
        };
      };
    };
  };
  if (instance->_waitDeclarations.empty()) {
    globals.insertContainer(instance->_waitingClassDeclaration);
    std::vector<MissingSubClassGeneration>::iterator subIterEnd
        = instance->_subGenerations.end();
    std::vector<MissingSubClassGeneration>::iterator subIter
        = instance->_subGenerations.begin();
    /* class_decl */ list* parentDeclList = NULL;
    int parentDeclPosition = 0;
    int subIndex = 0;
    assert(instance->_subGenerations.empty() || (instance
        ->_waitingClassDeclaration->tag_translation_unit_decl == COMPOUND
          && instance->_waitingClassDeclaration->cons_translation_unit_decl
            .Compound.body->is_some));
    while (subIter != subIterEnd && (!subIter->_waitingSubClassDecl
        || subIter->removeWaitWithinClass(instance->key(), parentDeclList,
             (/* class_decl */ list*) &instance->_waitingClassDeclaration
               ->cons_translation_unit_decl.Compound.body->content.container,
             parentDeclPosition, subIter->_parentPosition - subIndex))) {
      solve(*subIter, *instance, globals);
      ++subIter; ++subIndex;
    };
    if (subIter != subIterEnd) {
      // [TODO] use parentDeclList and subIter->_parentPosition
      //   instead of a new list.
      /* class_decl */ list subList = (list) instance->_waitingClassDeclaration
          ->cons_translation_unit_decl.Compound.body->content.container;
      assert(subList);
      while (subList) {
        class_decl classElement = (class_decl) subList->element.container;
        bool isEqual = classElement == subIter->_waitingSubClassDecl;
        if (!isEqual)
          isEqual = classElement->tag_class_decl == CCOMPOUND
            && subIter->_waitingSubClassDecl->tag_class_decl == CCOMPOUND
            && !strcmp(classElement->cons_class_decl.CCompound.name,
                subIter->_waitingSubClassDecl->cons_class_decl.CCompound.name)
            && tkind_equal(
                classElement->cons_class_decl.CCompound.template_kind,
                subIter->_waitingSubClassDecl->cons_class_decl
                  .CCompound.template_kind);
        if (isEqual) {
          addWaitFor(*subIter, subIter->_waitingSubClassDecl, instance, globals,
            classElement != subIter->_waitingSubClassDecl /* shouldBeSubkey */);
          ++subIter; ++subIndex;
          while (subIter != subIterEnd && (!subIter->_waitingSubClassDecl
              || subIter->removeWaitWithinClass(instance->key(), parentDeclList,
                (/* class_decl */ list*) &instance->_waitingClassDeclaration
                  ->cons_translation_unit_decl.Compound.body->content.container,
                parentDeclPosition, subIter->_parentPosition - subIndex))) {
            solve(*subIter, *instance, globals);
            ++subIter; ++subIndex;
          };
          if (subIter == subIterEnd)
            break;
        };
        subList = subList->next;
      };
      assert(subIter == subIterEnd);
    };

    instance->_waitingClassDeclaration = NULL;
    instance->_subGenerations.clear();
    MissingDecl::WaitingDecls::iterator iterEnd
        = instance->_waitingDecls.end();
    for (MissingDecl::WaitingDecls::iterator iter
        = instance->_waitingDecls.begin(); iter != iterEnd; ++iter) {
      if ((*iter)->solve(instance->_key, globals, *this)) {
        KeyInfo* toLocalDelete = *iter;
        ContentTable::iterator localFound = _content.find(toLocalDelete);
        assert(localFound != _content.end() && *localFound == toLocalDelete);
        _content.erase(localFound);
        *iter = new KeyInfo(**iter);
        _content.insert(*iter);
        delete toLocalDelete;
      };
    };
    instance->_waitingDecls.clear();

    ContentTable::iterator found = _content.find(instance);
    assert(found != _content.end());
    _content.erase(found);
    _content.insert(new KeyInfo(*instance));
  }
  else {
    translation_unit_decl definition = instance->_waitingClassDeclaration;
    assert(definition->tag_translation_unit_decl == COMPOUND);
    translation_unit_decl declaration = translation_unit_decl_Compound(
        copy_loc(definition->cons_translation_unit_decl.Compound.loc),
        decl_or_impl_name_dup(definition->cons_translation_unit_decl
            .Compound.name),
        definition->cons_translation_unit_decl.Compound.kind,
        opt_none() /* inherits */, opt_none() /* body */,
        false /* has_virtual */, tkind_dup(
            definition->cons_translation_unit_decl.Compound.template_kind),
        definition->cons_translation_unit_decl.Compound.is_extern_c_context,
        definition->cons_translation_unit_decl.Compound.is_ghost);
    globals.insertContainer(declaration);
    MissingClassGeneration* missingInstance
      = new MissingClassGeneration(*instance);
    enableNotificationFromBeforeReplaceWaiting(
        missingInstance->_waitDeclarations, instance->_waitingDecls,
        missingInstance, false /* mayHaveInstanceClass */);

    MissingDecl::WaitingDecls::iterator iterEnd
        = instance->_waitingDecls.end();
    for (MissingDecl::WaitingDecls::iterator iter
        = instance->_waitingDecls.begin(); iter != iterEnd; ++iter)
      (*iter)->replaceWaitingBy(missingInstance->key(),
          missingInstance->_waitDeclarations);
    instance->_waitingDecls.clear();
    ContentTable::iterator found = _content.find(instance);
    assert(found != _content.end());
    _content.erase(found);
    _content.insert(missingInstance);
    std::set<const clang::Decl*>::const_iterator
      subIterEnd = missingInstance->_subWaitDeclarations.end(),
      subIter = missingInstance->_subWaitDeclarations.begin();
    for (; subIter != subIterEnd; ++subIter) {
      KeyInfo locateKey(*subIter);
      ContentTable::iterator found = _content.lower_bound(&locateKey);
      if (found != _content.end() && (*found)->_key == *subIter) {
        std::vector<KeyInfo*>* waitingDecls = NULL;
        if ((*found)->isInstanceClass())
          waitingDecls = &((InstanceClassGeneration*) *found)->_waitingDecls;
        else {
          assert((*found)->isMissingDecl());
          waitingDecls = &((MissingDecl*) (*found))->waitingDecls();
        };
        MissingDecl::WaitingDecls::const_iterator
          endFindIter = waitingDecls->end(), findIter = waitingDecls->begin();
        bool hasFound = false;
        for (; !hasFound && findIter != endFindIter; ++findIter)
          hasFound = *findIter == missingInstance;
        if (!hasFound)
          waitingDecls->push_back(missingInstance);
      }
      else {
        MissingDecl* newMissing = new MissingDecl(*subIter);
        _content.insert(found, newMissing);
        newMissing->_waitingDecls.push_back(missingInstance);
      };
    }
  };
  delete instance;
}

VisitTable::MissingClassGeneration&
VisitTable::addIncompleteClass(const clang::RecordDecl* decl,
    std::vector<const clang::Decl*>& waitDeclarations,
    translation_unit_decl classDecl) {
  assert(!waitDeclarations.empty());
  KeyInfo locateKey(decl);
  ContentTable::iterator found = _content.lower_bound(&locateKey);
  MissingClassGeneration* result;
  if (found != _content.end() && (*found)->_key == decl) {
    assert((*found)->isMissingDecl());
    MissingDecl* oldMissing = (MissingDecl*) *found;
    result = new MissingClassGeneration(decl, classDecl);
    waitDeclarations.swap(result->_waitDeclarations);
    _content.erase(found);
    _content.insert(result);
    enableNotificationFromBeforeReplaceWaiting(result->_waitDeclarations,
        oldMissing->_waitingDecls, NULL /* originDependencies */,
        false /* mayHaveInstanceClass */);

    MissingDecl::WaitingDecls::iterator iterEnd
        = oldMissing->_waitingDecls.end();
    for (MissingDecl::WaitingDecls::iterator iter
        = oldMissing->_waitingDecls.begin(); iter != iterEnd; ++iter)
      (*iter)->replaceWaitingBy(decl, result->_waitDeclarations);
    delete oldMissing;
  }
  else {
    result = new MissingClassGeneration(decl, classDecl);
    waitDeclarations.swap(result->_waitDeclarations);
    _content.insert(found, result);
  };
  return *result;
}

VisitTable::MissingFunctionGeneration&
VisitTable::addIncompleteFunction(const clang::FunctionDecl* decl,
    std::vector<const clang::Decl*>& waitDeclarations,
    translation_unit_decl functionDecl,
    translation_unit_decl functionBareDecl) {
  assert(!waitDeclarations.empty());
  KeyInfo locateKey(decl);
  ContentTable::iterator found = _content.lower_bound(&locateKey);
  MissingFunctionGeneration* result;
  if (found != _content.end() && (*found)->_key == decl) {
    assert((*found)->isMissingDecl());
    MissingDecl* oldMissing = (MissingDecl*) *found;
    result= new MissingFunctionGeneration(decl, functionDecl, functionBareDecl);
    waitDeclarations.swap(result->_waitDeclarations);
    _content.erase(found);
    _content.insert(result);
    enableNotificationFromBeforeReplaceWaiting(result->_waitDeclarations,
        oldMissing->_waitingDecls, result, true /* mayHaveInstanceClass */);

    MissingDecl::WaitingDecls::iterator iterEnd
        = oldMissing->_waitingDecls.end();
    for (MissingDecl::WaitingDecls::iterator iter
        = oldMissing->_waitingDecls.begin(); iter != iterEnd; ++iter)
      (*iter)->replaceWaitingBy(decl, result->_waitDeclarations);
    delete oldMissing;
  }
  else {
    result= new MissingFunctionGeneration(decl, functionDecl, functionBareDecl);
    waitDeclarations.swap(result->_waitDeclarations);
    std::vector<const clang::Decl*>::iterator
      absentIterEnd = result->_waitDeclarations.end();
    for (std::vector<const clang::Decl*>::iterator
        absentIter = result->_waitDeclarations.begin();
        absentIter != absentIterEnd; ++absentIter) {
      KeyInfo locateKey(*absentIter);
      ContentTable::const_iterator found = _content.find(&locateKey);
      if (found == _content.end()) {
        MissingDecl* newMissing = new MissingDecl(*absentIter);
        _content.insert(newMissing);
        newMissing->_waitingDecls.push_back(result);
      }
      else if ((*found)->isMissingDecl()) { // has locally been found after
        if (((MissingDecl*) *found)->_waitingDecls.empty()
            || ((MissingDecl*) *found)->_waitingDecls.back() != result)
          ((MissingDecl*) *found)->_waitingDecls.push_back(result);
        else {
          int index = absentIter - result->_waitDeclarations.begin();
          result->_waitDeclarations.erase(absentIter);
          absentIter =  result->_waitDeclarations.begin() + index - 1;
          absentIterEnd =  result->_waitDeclarations.end();
        };
      }
      else if ((*found)->isInstanceClass()) {
        if (((InstanceClassGeneration*) *found)->_waitingDecls.empty()
            ||((InstanceClassGeneration*) *found)->_waitingDecls.back()!=result)
          ((InstanceClassGeneration*) *found)->_waitingDecls.push_back(result);
        else {
          int index = absentIter - result->_waitDeclarations.begin();
          result->_waitDeclarations.erase(absentIter);
          absentIter =  result->_waitDeclarations.begin() + index - 1;
          absentIterEnd =  result->_waitDeclarations.end();
        };
      }
      else { // should not occur
        int index = absentIter - result->_waitDeclarations.begin();
        result->_waitDeclarations.erase(absentIter);
        absentIter =  result->_waitDeclarations.begin() + index - 1;
        absentIterEnd =  result->_waitDeclarations.end();
      };
    }
    _content.insert(found, result);
  };
  return *result;
}
