/**************************************************************************/
/*                                                                        */
/*  This file is part of Frama-C.                                         */
/*                                                                        */
/*  Copyright (C) 2007-2012                                               */
/*    CEA (Commissariat à l'énergie atomique et aux énergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  All rights reserved.                                                  */
/*  Contact CEA LIST for licensing.                                       */
/*                                                                        */
/**************************************************************************/

/* built-ins specific to C++ analysis. */
#ifndef FRAMA_CXX
#define FRAMA_CXX

#ifdef __powerpc__
#define FCLANG_SIZE_T unsigned
#else
#ifdef __i386__
#define FCLANG_SIZE_T unsigned
#else
#ifdef __x86_64__
#define FCLANG_SIZE_T unsigned long
#else
#error "unknown architecture"
#endif
#endif
#endif

typedef FCLANG_SIZE_T __fc_builtin_size_t;

/* access to C builtins */
extern "C" {
#include "__fc_builtin.h"
}

/* implementation of std::min and std::max */
namespace std {
  template<class T> const T& min (const T& a, const T& b) {
    return (b < a ? b : a);
  }

  template<class T> const T& max (const T& a, const T& b) {
    return (a < b ? b : a);
  }

  // handling of gnu-specific assignment operators
  template<class T> T& min_assgn(T& a, const T& b) {
    a = min(a,b);
    return a;
  }

  template<class T> T& max_assgn(T& a, const T& b) {
    a = max(a,b);
    return a;
  }

}

/* experimental feature on scope analysis:
   all destructors calls will end with a call to CXX_destructor, in order to
   invalidate any reference to the object */
#ifdef CC_SCOPE

// dummy predicate, that is mainly used to inform the cxx plugin that it
// should enable the scope analysis. More refined versions of it are then
// generated for each class
/*@ predicate pointee_in_scope(void* x); */

#endif //CC_SCOPE

#endif //FRAMA_CXX
