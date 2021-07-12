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
//   Definition of a generic descent parser.
//

#ifndef DescentParserH
#define DescentParserH

#include <iostream>
#include <list>
#include <vector>
#include <memory>
#include <assert.h>
#include <cstring>

/** @file */

/*! @def DefineParameters(ReservedBytes, FormatParameters)
 *  @brief Define many bitfields likely to be grouped. This definition is
 *    compatible with a class hierarchy as soon as the sum of the reserved bits
 *    does not exceed 32.
 *
 *  ReservedBytes is the number of bits reseved for the current class. \n
 *  FormatParameters is the inherited class that contains the params() and 
 *    queryParams() definition -- it is a class derived from FormatParameters.
 *    \n
 *  For example:
 *  \code{cpp}
 *  class Foo : public FormatParameters {
 *  protected:
 *    DefineParameters(5, FormatParameters)
 *  };
 *  \endcode
 *  is equivalent to
 *  \code{cpp}
 *    unsigned ownField : 5;
 *  \endcode
 *  But it has more grouping capabilities.
 */
#define DefineParameters(ReservedBytes, FormatParameters)                      \
  unsigned int& params() { return FormatParameters::params(); }                \
  const unsigned int& queryParams() const                                      \
    { return FormatParameters::queryParams(); }                                \
  static const int START_OF_MASK = FormatParameters::END_OF_MASK;              \
  static const int END_INHERITED_OF_MASK = FormatParameters::END_OF_MASK;      \
  static const int END_OF_MASK = ReservedBytes + START_OF_MASK;                \
  static const unsigned int MASK                                               \
    = ((1 << END_OF_MASK)-1) & ~((1 << START_OF_MASK)-1);                      \
  void clearOwnField() { params() &= ~MASK; }                                  \
  void mergeOwnField(int uField)                                               \
    { params() |= (MASK & (uField << START_OF_MASK)); }                        \
  void intersectOwnField(int uField)                                           \
    { params() &= (MASK & (uField << START_OF_MASK)); }                        \
  void setOwnField(int uField)                                                 \
    { FormatParameters::params() &= ~MASK;                                     \
      params() |= (MASK & (uField << START_OF_MASK));                          \
    }                                                                          \
  bool hasOwnField() const { return queryParams() & MASK; }                    \
  int queryOwnField() const { return (queryParams() & MASK) >> START_OF_MASK; }\
  void setLocalField() { params() &= ((1 << END_OF_MASK)-1); }                 \
  bool hasFieldExtensions() const                                              \
    { return (queryParams() & ~((1 << END_OF_MASK)-1)) != 0; }                 \
  unsigned int queryFieldExtensions() const                                    \
    { return queryParams() >> END_OF_MASK; }

/*! @def DefineSubParameters(Name, ReservedBytes, FormatParameters)
 *  @brief Create a subfield in a given group of bitfields. The sum of
 *    ReservedBytes for all the subfields should be equal to the
 *    ReservedBytes of the group of bitfields.
 *
 *  For example:
 *  \code{cpp}
 *  class Foo : public FormatParameters {
 *  protected:
 *    DefineParameters(5, FormatParameters)
 *    DefineSubParameters(Type, 3, INHERITED)
 *    DefineSubParameters(Verbose, 1, Type)
 *    DefineSubParameters(Pretty, 1, Verbose)
 *  };
 *  \endcode
 *  is equivalent to
 *  \code{cpp}
 *    unsigned type : 3;
 *    bool verbose : 1;
 *    bool pretty : 1;
 *  \endcode
 *  But it has more grouping capabilities.
 */
#define DefineSubParameters(Name, ReservedBytes, FormatParameters)             \
  static const int START_##Name##_OF_MASK = END_##FormatParameters##_OF_MASK;  \
  static const int END_##Name##_OF_MASK                                        \
    = ReservedBytes + END_##FormatParameters##_OF_MASK;                        \
  static const unsigned int Name##_MASK                                        \
    = ((1 << END_##Name##_OF_MASK)-1)                                          \
        & ~((1 << END_##FormatParameters##_OF_MASK)-1);                        \
  void clear##Name##Field() { params() &= ~Name##_MASK; }                      \
  void merge##Name##Field(int uField)                                          \
    { params() |= (Name##_MASK & (uField << START_##Name##_OF_MASK)); }        \
  void intersect##Name##Field(int uField)                                      \
    { params() &= (~Name##_MASK | (Name##_MASK                                 \
          & (uField << START_##Name##_OF_MASK)));                              \
    }                                                                          \
  void set##Name##Field(int uField)                                            \
    { params() &= ~Name##_MASK;                                                \
      params() |= (Name##_MASK & (uField << START_##Name##_OF_MASK));          \
    }                                                                          \
  bool has##Name##Field() const { return queryParams() & Name##_MASK; }        \
  int query##Name##Field() const                                               \
    { return (queryParams() & Name##_MASK) >> START_##Name##_OF_MASK; }

/*! @class FormatParameters
 *  @brief Defines a base class whose derived classes have grouping
 *    bitfield capabilities.
 *
 *  @sa{ DefineParameters, DefineSubParameters }
 */
class FormatParameters {
private:
  unsigned int _params;

protected:
  unsigned int& params() { return _params; }
  const unsigned int& queryParams() const { return _params; }
  static const int END_OF_MASK = 0;
  static const unsigned int MASK = 0;

  public:
  FormatParameters() : _params(0) {}
  FormatParameters(const FormatParameters& source) : _params(source._params) {}
  FormatParameters& operator=(const FormatParameters& source)
    { _params = source._params;
      return *this;
    }
};

namespace Parser {

/*! @class TTextBuffer
 *  @brief Defines a stream of characters that have been read by the Lexer.
 */
template<typename CharType>
class TTextBuffer {
public:
  typedef std::basic_string<CharType> StringBuffer;
  typedef std::list<StringBuffer*> BuffersList;

private:
  typedef TTextBuffer<CharType> thisType;
  BuffersList _buffers;
  std::unique_ptr<StringBuffer> _current;
  unsigned _position;

  void performMove()
    { int defaultSize = _current->capacity();
      _buffers.push_back(_current.release());
      _current.reset(new StringBuffer);
      _current->reserve(defaultSize);
    }
  void completeRead(const CharType* string, int length);
  void completeRead(const StringBuffer& source, size_t position, size_t count);
  void completeWrite(StringBuffer& out);
  CharType completeQueryChar(int index) const;
  int queryPlace() const
    { return _current.get() ? _current->capacity() - _position : 0; }

public:
  TTextBuffer(int defaultLength=5000)
    : _current(new StringBuffer), _position(0)
    { _current->reserve(defaultLength); }


  TTextBuffer(const thisType& source)
    : _buffers(source._buffers),
      _current(const_cast<thisType&>(source)._current.release()),
      _position(source._position) {}

  void clear()
    { typename BuffersList::iterator iterEnd = _buffers.end();
      for(typename BuffersList::iterator iter = _buffers.begin();
          iter != iterEnd; ++iter) {
        StringBuffer* buffer = *iter;
        if (buffer)
          { delete buffer; buffer = NULL; };
      };
      _current->clear();
    }
  thisType& operator<<(CharType ch);
  thisType& operator<<(const CharType* string);
  thisType& readFrom(const StringBuffer& text, size_t position, size_t length);
  thisType& operator>>(StringBuffer& buffer);
  bool isEmpty() const
    { return _buffers.empty() && _current->length() == _position; }
  bool hasOnlyCurrent() const { return _buffers.empty(); }
  const char* current()
    { assert(_buffers.empty() && _current.get()
          && _position <= _current->length());
      return &_current->c_str()[_position];
    }
  CharType getChar(int index) const
    { CharType result;
      if (_current->empty()) {
        assert(_current.get() && ((int) _position >= -index)
            && (index + (int) _position) <= (int) _current->length());
        result = _current->c_str()[index + _position];
      }
      else
        result = completeQueryChar(index); 
      return result;
    }
};

template<typename CharType>
inline TTextBuffer<CharType>&
TTextBuffer<CharType>::operator<<(CharType ch) {
  if (queryPlace() == 0)
    performMove();
  _current->append(1, ch);
  return *this;
}

template<typename CharType>
inline TTextBuffer<CharType>&
TTextBuffer<CharType>::operator<<(const CharType* string) {
  int length = strlen(string);
  if (queryPlace() < length)
    completeRead(string, length);
  else
    _current->append(string, length);
  return *this;
}

template<typename CharType>
inline TTextBuffer<CharType>&
TTextBuffer<CharType>::readFrom(const StringBuffer& string, size_t position,
    size_t count) {
  if (queryPlace() < (int) count)
    completeRead(string, position, count);
  else
    _current->append(string, position, count);
  return *this;
}

template<class TypeSubString>
inline TTextBuffer<TypeSubString>&
TTextBuffer<TypeSubString>::operator>>(StringBuffer& string) {
  if (!_buffers.empty())
    completeWrite(string);
  else {
    string.append(*_current);
    _current->clear();
  };
  return *this;
}

typedef TTextBuffer<char> TextBuffer;

/******************************************/
/* D�finition of the template TStateStack */
/******************************************/

/*! @class Base
 *  @brief Gives an access to parsing rules. The parsing rules correspond to
 *    inherited attributes in attribute grammars. They should inherit from
 *    Base::RuleResult. The synthesized attributes may be stored in the
 *    fields of the inherited attributes.
 */
class Base {
public:
  class RuleResult {
  public:
    virtual ~RuleResult() {}
    virtual RuleResult* clone() const { return new RuleResult(*this); }
  };
  enum ReadResult
    { RRNeedChars, RRContinueLexing, RRHasToken, RRContinueParsing,
      RRFinished
    };
};

/*! @class TStateStack
 *  @brief Represents the stack of the grammar rules waiting for a reduction.
 *  The methods shift and reduce enable to push and to pop on the stack.
 */
template <class TypeArguments>
class TStateStack : public Base {
private:
  typedef TStateStack<TypeArguments> thisType;

public:
  typedef TypeArguments ParseArgument;
  class VirtualParseState {
  private:
    int _point;
    std::unique_ptr<RuleResult> _ruleResult;

  public:
    VirtualParseState() : _point(0) {}
    VirtualParseState(const VirtualParseState& source)
      : _point(source._point),
        _ruleResult(source._ruleResult.get()
            ? source._ruleResult->clone() : NULL) {}
    virtual ~VirtualParseState() {}

    virtual VirtualParseState* clone() const
      { return new VirtualParseState(*this); }
    int& point() { return _point; }
    const int& point() const { return _point; }
    virtual ReadResult operator()(TStateStack<TypeArguments>& stateStack,
        ParseArgument& arguments) 
      { assert(false); return RRFinished; }

    bool hasResult() const { return _ruleResult.get(); }
    RuleResult& getResult() const { return *_ruleResult; }
    void setResult(RuleResult* ruleResult)
      { assert(!_ruleResult.get());
        _ruleResult.reset(ruleResult);
      }
    void changeResult(RuleResult* ruleResult)
      { _ruleResult.reset(ruleResult); }
    void freeResult() { _ruleResult.reset(); }
    RuleResult* extractResult() { return _ruleResult.release(); }
  };

  template <class TypeObject, typename ReadPointerMethod>
  class TParseState : public VirtualParseState {
  private:
    ReadPointerMethod _readMethod;
    TypeObject* _object;
    typedef VirtualParseState inherited;
    typedef TParseState<TypeObject, ReadPointerMethod> thisType;

  public:
    TParseState() : _object(NULL), _readMethod(NULL) {}
    TParseState(TypeObject& object, const ReadPointerMethod& readMethodSource)
      : _readMethod(readMethodSource), _object(&object) {}
    TParseState(const thisType& source)
      : inherited(source), _readMethod(source._readMethod),
        _object(source._object) {}
    virtual VirtualParseState* clone() const { return new thisType(*this); }

    virtual ReadResult operator()(
        TStateStack<TypeArguments>& stateStack, ParseArgument& arguments) 
      { return (_object->*_readMethod)(stateStack, arguments); }
    const ReadPointerMethod& getStateMethod() const { return _readMethod; }
    void change(TypeObject& object, ReadPointerMethod readMethod, int point)
      { _object = &object;
        _readMethod = readMethod;
        inherited::point() = point;
      }
    bool hasObjectRead(const TypeObject& object, ReadPointerMethod readMethod)
      { return (_object == &object) && (_readMethod == readMethod); }
    bool hasMethodRead(ReadPointerMethod readMethod)
      { return (_readMethod == readMethod); }
  };

  template <class TypeObject, typename ReadPointerMethod,
            class TypeParseMultiState>
  class TLevelParseState : public VirtualParseState {
  private:
    ReadPointerMethod _readMethod;
    TypeObject* _object;
    typedef VirtualParseState inherited;
    typedef TLevelParseState<TypeObject, ReadPointerMethod, TypeParseMultiState>
      thisType;

  public:
    TLevelParseState() : _object(NULL), _readMethod(NULL) {}
    TLevelParseState(TypeObject& object, const ReadPointerMethod& readMethod)
      : _readMethod(readMethod), _object(&object) {}
    TLevelParseState(const thisType& source)
      : inherited(source), _readMethod(source._readMethod),
        _object(source._object) {}
    virtual VirtualParseState* clone() const { return new thisType(*this); }

    virtual ReadResult operator()(TStateStack<TypeArguments>& stateStack,
        ParseArgument& arguments) 
      { return (_object->*_readMethod)((TypeParseMultiState&) stateStack,
          (typename TypeParseMultiState::ParseArgument&) arguments);
      }
    const ReadPointerMethod& getStateMethod() const { return _readMethod; }
    void change(TypeObject& object, ReadPointerMethod readMethod, int point)
      { _object = &object;
        _readMethod = readMethod;
        inherited::point() = point;
      }
    bool hasObjectRead(const TypeObject& object, ReadPointerMethod readMethod)
        const
      { return (_object == &object) && (_readMethod == readMethod); }
    bool hasMethodRead(ReadPointerMethod readMethod) const
      { return (_readMethod == readMethod); }
  };

protected:
  typedef std::vector<VirtualParseState*> ArrayParseStates;

private:
  ArrayParseStates _states;

protected:
  ArrayParseStates& states() { return _states; }
  const ArrayParseStates& states() const { return _states; }

  template <class TypeObject, typename ReadPointerMethod, class SpecializedThis>
  thisType& _shift(TypeObject& object, ReadPointerMethod parseMethod,
      SpecializedThis* thisState)
    { _states.add(new TLevelParseState<TypeObject, ReadPointerMethod,
          SpecializedThis>(object, parseMethod));
      return *this;
    }
  template <class TypeObject, typename ReadPointerMethod, class SpecializedThis>
  SpecializedThis& _change(TypeObject& object, ReadPointerMethod parseMethod,
      int point, SpecializedThis* thisState)
    { typedef TLevelParseState<TypeObject, ReadPointerMethod,
          SpecializedThis> ParseState;
      assert(!_states.empty()
          && dynamic_cast<ParseState*>(_states.back()) != NULL);
      ((ParseState&) *_states.back()).change(object, parseMethod, point);
      return (SpecializedThis&) *this;
    }
  template <class TypeObject, typename ReadPointerMethod, class SpecializedThis>
  bool _tisAlive(TypeObject& object, ReadPointerMethod parseMethod, int uLevel,
      SpecializedThis* thisState)
    { typedef TLevelParseState<TypeObject, ReadPointerMethod, SpecializedThis>
          ParseState;
      return (_states.count() > uLevel)
          && dynamic_cast<ParseState*>(&_states[uLevel])
          && ((ParseState&) _states[uLevel]).hasObjectRead(object, parseMethod);
    }
  template <class TypeObject, typename ReadPointerMethod, class SpecializedThis>
  bool _tisAlive(TypeObject* object, ReadPointerMethod parseMethod, int level,
      SpecializedThis* thisState)
    { typedef TLevelParseState<TypeObject, ReadPointerMethod, SpecializedThis>
          ParseState;
      return (_states.size() > level)
          && dynamic_cast<ParseState*>(_states[level])
          && ((ParseState&) *_states[level]).hasMethodRead(parseMethod);
    }
  template <class TypeObject, typename ReadPointerMethod, class SpecializedThis>
  bool _tisParentAlive(TypeObject* object, ReadPointerMethod parseMethod,
      SpecializedThis* thisState)
    { typedef TLevelParseState<TypeObject, ReadPointerMethod, SpecializedThis>
          ParseState;
      int count = _states.size();
      return (count > 1) && dynamic_cast<ParseState*>(_states[count-2])
          && ((ParseState&) *_states[count-2]).hasMethodRead(parseMethod);
    }

public:
  TStateStack() {}
  TStateStack(const thisType& source)
    { typename ArrayParseStates::const_iterator iterEnd = source._states.end();
      for (typename ArrayParseStates::const_iterator
          iter = source._states.begin(); iter != iterEnd; ++iter) {
        VirtualParseState* state = *iter;
        _states.push_back(state->clone());
      };
    }
  ~TStateStack()
    { typename ArrayParseStates::iterator iterEnd = _states.end();
      for (typename ArrayParseStates::iterator iter = _states.begin();
          iter != iterEnd; ++iter) {
        VirtualParseState*& state = *iter;
        if (state)
          { delete state; state = NULL; }
      };
    }

  void clear()
    { typename ArrayParseStates::iterator iterEnd = _states.end();
      for (typename ArrayParseStates::iterator iter = _states.begin();
          iter != iterEnd; ++iter) {
        VirtualParseState*& state = *iter;
        if (state)
          { delete state; state = NULL; }
      };
      _states.clear();
    }
  void swap(thisType& source) { _states.swap(source._states); }

  ReadResult parse(ParseArgument& arguments)
    { if (_states.empty()) return Base::RRFinished;
      return (*_states.back())(*this, arguments);
    }
  template <class TypeObject, typename ReadPointerMethod>
  thisType& shift(TypeObject& object, ReadPointerMethod parseMethod)
    { _states.push_back(new TParseState<TypeObject, ReadPointerMethod>(
          object, parseMethod));
      return *this;
    }
  template <class TypeObject, typename ReadPointerMethod>
  thisType& change(TypeObject& object, ReadPointerMethod parseMethod, int point)
    { typedef TParseState<TypeObject, ReadPointerMethod> ParseState;
      assert(!_states.empty()
          && dynamic_cast<ParseState*>(_states.back()) != NULL);
      ((ParseState&) *_states.back()).change(object, parseMethod, point);
      return *this;
    }
  template <class TypeObject, typename ReadPointerMethod>
  bool tisAlive(TypeObject& object, ReadPointerMethod parseMethod, int level)
    { typedef TParseState<TypeObject, ReadPointerMethod> ParseState;
      int count = _states.size();
      return (count > level) && dynamic_cast<ParseState*>(_states[level])
        && ((ParseState&) *_states[level]).hasObjectRead(object, parseMethod);
    }
  template <class TypeObject, typename ReadPointerMethod>
  bool tisAlive(TypeObject* object, ReadPointerMethod parseMethod, int level)
    { typedef TParseState<TypeObject, ReadPointerMethod> ParseState;
      int count = _states.size();
      return (count > level) && dynamic_cast<ParseState*>(&_states[level])
        && ((ParseState&) _states[level]).hasMethodRead(parseMethod);
    }
  template <class TypeObject, typename ReadPointerMethod>
  bool tisParentAlive(TypeObject* object, ReadPointerMethod parseMethod)
    { typedef TParseState<TypeObject, ReadPointerMethod> ParseState;
      int count = _states.size();
      return (count > 1) && dynamic_cast<ParseState*>(&_states[count-2])
        && ((ParseState&) _states[count-2]).hasMethodRead(parseMethod);
    }
  bool isAlive(int level, int point) const
    { return (_states.size() > level) && (_states[level].point() == point); }
  bool isLessThan(int uLevel, int uPoint) const
    { return (_states.size() > uLevel) && (_states[uLevel].point() < uPoint); }
  thisType& reduce()
    { assert(!_states.empty());
      VirtualParseState* oldState = _states.back();
      if (oldState) delete oldState;
      _states.pop_back();
      return *this;
    }

  const int& point() const
    { assert(!_states.empty()); return _states.back()->point(); }
  int& point() { return _states.back()->point(); }
  int getLevel() const { return _states.size()-1; }

  VirtualParseState& last()
    { assert(!_states.empty()); return *_states.back(); }
  const VirtualParseState& last() const
    { assert(!_states.empty()); return *_states.back(); }
  bool isEmpty() const { return _states.empty(); }
  const VirtualParseState& upLast() const
    { typename ArrayParseStates::const_reverse_iterator iter = _states.rbegin();
      assert(iter != _states.rend());
      ++iter;
      assert(iter != _states.rend());
      return **iter;
    }

  void absorbRuleResult(RuleResult* result)
    { last().setResult(result); }
  void changeRuleResult(RuleResult* result)
    { last().changeResult(result); }
  void freeRuleResult() { last().freeResult(); }
  bool hasRuleResult() const { return last().hasResult(); }
  bool hasParentRuleResult() const { return upLast().hasResult(); }

  class ObjectReference {
  private:
    RuleResult& _result;

  public:
    ObjectReference(RuleResult& result) : _result(result) {}
    ObjectReference(const ObjectReference& orSource)
      : _result(orSource._result) {}

    template <class Type> operator Type*() const
      { return (Type*) &_result; }
  };

  class ObjectKeepReference {
  private:
    RuleResult* _result;

  public:
    ObjectKeepReference(RuleResult* result) : _result(result) {}
    ObjectKeepReference(const ObjectKeepReference& source)
      : _result(source._result)
      { const_cast<ObjectKeepReference&>(source)._result = NULL; }
    ~ObjectKeepReference() { if (_result) delete _result; }

    template <class Type> operator Type*()
      { assert(dynamic_cast<Type*>(_result));
        Type* result = (Type*) _result;
        _result = NULL;
        return result;
      }
  };

  class RuleAccess {
  public:
    template <class TypeObject>
    class TCastFromRule {
    private:
      TypeObject* poObject;
      
    public:
      explicit TCastFromRule(const ObjectReference& result)
        : poObject((TypeObject*) result) {}
      operator TypeObject&() const { return *poObject; }
      TypeObject& operator*() const { return *poObject; }
      TypeObject* operator->() const { return poObject; }
      TypeObject* get() const { return poObject; }
    };
  };
  
  RuleResult* extractRuleResult()
    { return last().extractResult(); }
  ObjectReference getRuleResult() const
    { return ObjectReference(last().getResult()); }
  ObjectReference getRuleResultAt(int uLevel) const
    { return ObjectReference(_states[uLevel].getResult()); }
  ObjectKeepReference extractSRuleResult()
    { return ObjectKeepReference(last().extractResult()); }
  ObjectReference getParentRuleResult() const
    { return ObjectReference(upLast().getResult()); }
};

} // end of namespace Parser

#endif // DescentParserH

