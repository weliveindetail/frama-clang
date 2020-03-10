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

// See http://refspecs.linuxfoundation.org/cxxabi-1.86.html

#ifndef __CXX_ABI_H

#define __CXX_ABI_H

#include <cstddef>
#include <typeinfo>

namespace __cxxabiv1 {

    class __fundamental_type_info: public std::type_info { };
    class __array_type_info: public std::type_info { };
    class __function_type_info: public std::type_info { };
    class __enum_type_info: public std::type_info { };
    class __class_type_info: public std::type_info { };

    class __si_class_type_info: public __class_type_info {
    public:
      const __class_type_info *__base_type;
    };

  struct __base_class_type_info {
  public:
    const __class_type_info *__base_type;
    long __offset_flags;
    enum __offset_flags_masks
      {
       __virtual_mask = 0x1,
       __public_mask = 0x2,
       __offset_shift = 8
      };
  };

  class __vmi_class_type_info: public __class_type_info {
  public:
    unsigned int __flags;
    unsigned int __base_count;
    __base_class_type_info __base_info[];
    enum __flags_masks
      {
       __non_diamond_repeat_mask = 0x1,
       __diamond_shaped_mask = 0x2
      };
    };

    class __pbase_type_info: public  std::type_info {
    public:
      unsigned int __flags;
      const std::type_info *__pointee;

      enum __masks
        {
         __const_mask = 0x1,
         __volatile_mask = 0x2,
         __restrict_mask = 0x4,
         __incomplete_mask = 0x8,
         __incomplete_class_mask = 0x10
        };
    };

    class __pointer_type_info: public __pbase_type_info { };

  class __pointer_to_member_type_info : public __pbase_type_info {
  public:
    const __class_type_info *__context;
  };

extern "C"
void* __dynamic_cast ( const void *sub,
                       const __class_type_info *src,
                       const __class_type_info *dst,
                       ptrdiff_t src2dst_offset);

extern "C" void __cxa_pure_virtual ();

extern "C" int __cxa_guard_acquire (__INT64_T *guard_object );

extern "C" void __cxa_guard_release ( __INT64_T *guard_object );

extern "C" void __cxa_guard_abort ( __INT64_T *guard_object );

extern "C" void * __cxa_vec_new (
  size_t element_count,
  size_t element_size,
  size_t padding_size,
  void (*constructor) ( void *),
  void (*destructor) ( void *) );

extern "C" void * __cxa_vec_new2 (
  size_t element_count,
  size_t element_size,
  size_t padding_size,
  void (*constructor) ( void *),
  void (*destructor) ( void *),
  void* (*alloc) ( size_t),
  void (*dealloc) ( void *) );

extern "C" void * __cxa_vec_new3 (
  size_t element_count,
  size_t element_size,
  size_t padding_size,
  void (*constructor) ( void *),
  void (*destructor) ( void *),
  void* (*alloc) ( size_t),
  void (*dealloc) ( void *, size_t) );

extern "C" void __cxa_vec_ctor (
  void *array_address,
  size_t element_count,
  size_t element_size,
  void (*constructor) ( void *),
  void (*destructor) ( void *) );

extern "C" void __cxa_vec_dtor (
  void *array_address,
  size_t element_count,
  size_t element_size,
  void (*destructor) ( void *) );

extern "C" void __cxa_vec_cleanup (
  void *array_address,
  size_t element_count,
  size_t element_size,
  void (*destructor) ( void *) );

extern "C" void __cxa_vec_delete (
  void *array_address,
  size_t element_size,
  size_t padding_size,
  void (*destructor) ( void *) );

extern "C" void __cxa_vec_delete2 (
  void *array_address,
  size_t element_size,
  size_t padding_size,
  void (*destructor) ( void *),
  void (*dealloc) ( void *) );

extern "C" void __cxa_vec_delete3 (
  void *array_address,
  size_t element_size,
  size_t padding_size,
  void (*destructor) ( void *),
  void (*dealloc) ( void *, size_t) );

extern "C" void __cxa_vec_cctor (
  void *dest_array,
  void *src_array,
  size_t element_count,
  size_t element_size,
  void (*constructor) (void *, void *),
  void (*destructor) (void *));

// TODO: initialization priority

extern "C" int __cxa_atexit ( void (*f)(void *), void *p, void *d );

extern "C" void __cxa_finalize ( void *d );

extern "C" char* __cxa_demangle (
  const char* mangled_name,
  char* buf,
  size_t* n,
  int* status);

}

namespace abi = __cxxabiv1;


#endif

/*
  Local Variables:
  mode: C++
  End:
*/
