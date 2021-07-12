(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-Clang                                      *)
(*                                                                        *)
(*  Copyright (C) 2012-2021                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file LICENSE).                      *)
(*                                                                        *)
(**************************************************************************)

(** Managing conversion environment *)
open Intermediate_format
open Cabs

type env

val empty_env: env

val add_c_global: env -> definition -> env
(** add a global c definition to the list of translated items. The ghost
    status of the definition is given by the env itself (see
    {! Convert_env.is_ghost })
*)

val get_c_globals: env -> (bool * definition) list
(** get the list of translated global definitions, in the order
    in which they were added.
*)

val fatal: env -> ('a,Format.formatter,unit,'b) format4 -> 'a

val temp_name: env -> string -> string
(** [temp_name env prefix] returns a fresh name based on [prefix]. *)

val add_namespace: env -> qualification -> env
(** enter a new, inner namespace *)

val set_namespace: env -> qualified_name -> env
(** Sets the namespace to the one enclosing the corresponding symbol *)

val set_namespace_from_class: env -> (qualified_name * tkind) -> env
(** given the fully qualified name of a class, set the namespace to the inner
    of it *)

val get_namespace: env->qualification list
(** give the names of the nammespaces currently opened. Newest is last. *)

val reset_namespace: env -> env
 (** close the most recently opened namespace. *)

val class_name_from_qualifications:
  env -> qualification list -> (qualified_name * tkind) option

val class_type_from_qualifications: env -> qualification list -> typ

val add_local_var: env -> string -> typ -> env

val add_formal_parameters: env -> arg_decl list -> env

val add_global_var: env -> qualified_name -> typ -> env
(** [add_global_var env name is_extern_c typ] *)

val get_local_var: env -> string -> typ
(** @raise AbortFatal if not found *)

(** [unscope current old] returns the same environment as [current] except
    for local vars, that are reset to the ones of [old]. *)
val unscope: env -> env -> env

val get_global_var: env -> qualified_name -> (bool * typ)
(** returns the type and whether the variable is an extern C one or not.
    @raise AbortFatal if not found *)

val set_loc: env -> location -> env

val get_loc: env -> cabsloc

val get_clang_loc: env -> location

val set_extern_c: env -> bool -> env

val is_extern_c: env -> bool

val set_ghost: env -> bool -> env

val is_ghost: env -> bool

val qualify: env -> string -> qualified_name

val set_current_func_name: env -> qualified_name -> env
(** set the current function name. Might also change the namespace if the
    function is fully qualified.
 *)

val get_current_func_name: env -> string

val set_current_return_type: env -> typ -> env

val get_current_return_type: env -> typ

val reset_func: env -> env
(** also reset the namespace if needed *)

val get_current_class: env -> Fclang_datatype.Qualified_name.t option

val set_current_class: env -> Fclang_datatype.Qualified_name.t -> env
(** also performs a {! set_namespace_from_class} *)

val reset_current_class: env -> env
(** also reset the namespace *)

val add_typedef: env -> qualified_name -> qual_type -> env

val get_typedef: env -> qualified_name -> qual_type
(** @raise AbortFatal if not found *)

val has_typedef: env -> qualified_name -> bool

val add_struct: env -> (qualified_name * tkind) -> (string * qual_type) list
    -> env

(** indicates that the given struct has some virtual member functions. *)
val virtual_struct: env -> (qualified_name * tkind) -> env

(** changes only the template parameters in the qualification.
    This function should be used for mangling.
 *)
val typedef_normalize : env -> qualified_name -> tkind
    -> (qualified_name * tkind)

val signature_normalize : env -> signature -> signature

val qual_type_normalize : env -> qual_type -> qual_type

val get_struct: env -> (qualified_name * tkind) -> (string * qual_type) list

val struct_has_virtual: env -> (qualified_name * tkind) -> bool

val add_default_constructor:
  env -> qualified_name -> signature -> env
(** adds the given constructor as the default constructor for the 
    appropriate class. Does nothing if such a constructor already exists.
 *)

val add_default_constructor_base:
  env -> qualified_name -> signature -> env
(** adds the given constructor as the default constructor for the 
    appropriate class when used as a base class of a parent.
    Does nothing if such a constructor already exists. The distinction is
    only meaningful for classes that have virtual bases.
 *)

val get_default_constructor:
  env -> (qualified_name * tkind) -> qualified_name * signature
  (** given a class name, returns the name and signature of its default
      constructor if it exists.
      @raise AbortFatal if no default constructor has been set for this class.
   *)

val get_option_default_constructor:
  env -> (qualified_name * tkind) -> (qualified_name * signature) option
  (** given a class name, returns the name and signature of its default
      constructor if it exists or None if no default constructor has been
      set for this class. *)

val get_option_default_constructor_base:
  env -> (qualified_name * tkind) -> (qualified_name * signature) option
  (** given a class name, returns the name and signature of its default
      constructor when used as a base class of a parent, if it exists,
      or None if no default constructor has been set for this class. *)

val add_copy_constructor:
  env -> qualified_name -> signature -> env

val add_copy_constructor_base:
  env -> qualified_name -> signature -> env
(** add a copy constructor for the class when it is used as a base class
    called from a parent. Only useful when the current class has virtual
    base classes. *)

val get_copy_constructor:
  env -> (qualified_name * tkind) -> qualified_name * signature

val get_option_copy_constructor:
  env -> (qualified_name * tkind) -> (qualified_name * signature) option

val get_option_copy_constructor_base:
  env -> (qualified_name * tkind) -> (qualified_name * signature) option
(** gets the copy constructor for the given class when used as a base class
    of a parent. Only used if the current class has virtual base classes. *)


val add_move_constructor:
  env -> qualified_name -> signature -> env

val add_move_constructor_base:
  env -> qualified_name -> signature -> env

val get_move_constructor:
  env -> (qualified_name * tkind) -> qualified_name * signature

val get_option_move_constructor:
  env -> (qualified_name * tkind) -> (qualified_name * signature) option

val get_option_move_constructor_base:
  env -> (qualified_name * tkind) -> (qualified_name * signature) option

val add_destructor:
  env -> (qualification list) -> env

val add_destructor_base:
  env -> (qualification list) -> env

val has_destructor:
  env -> (qualified_name * tkind) -> bool
val has_destructor_base:
  env -> (qualified_name * tkind) -> bool

val add_assign_operator:
  env -> qualified_name -> signature -> env

val add_assign_operator_base:
  env -> qualified_name -> signature -> env

val get_assign_operator:
  env -> (qualified_name * tkind) -> qualified_name * signature

val get_option_assign_operator:
  env -> (qualified_name * tkind) -> (qualified_name * signature) option

val get_option_assign_operator_base:
  env -> (qualified_name * tkind) -> (qualified_name * signature) option

val add_move_operator:
  env -> qualified_name -> signature -> env

val add_move_operator_base:
  env -> qualified_name -> signature -> env

val get_move_operator:
  env -> (qualified_name * tkind) -> qualified_name * signature

val get_option_move_operator:
  env -> (qualified_name * tkind) -> (qualified_name * signature) option

val get_option_move_operator_base:
  env -> (qualified_name * tkind) -> (qualified_name * signature) option

val add_aggregate: env -> qualified_name -> ckind -> tkind -> bool -> env
(** adds an aggregate type of the given kind. The boolean flag indicates
    whether the aggregate is an extern C type. *)

val get_aggregate: env -> (qualified_name * tkind) -> (ckind * bool)
(** @raise AbortFatal if not found *)

val is_extern_c_aggregate: env -> qualified_name -> tkind -> bool
(**@ raise AbortFatal if not found. *)

val struct_or_union: env -> (qualified_name * tkind) -> typ
(** returns the corresponding C++ typ, namely [Struct name t] or [Union name t].
    [name] must be an aggregate
    @raise AbortFatal if not found *)

val current_struct_or_union: env -> ckind

val is_anonymous: env -> bool
(** whether current class/union is anonymous *)

val get_class_name: env -> typ -> (qualified_name * tkind)
(** returns the name of the class bound to the given [typ], which can be
    either a class or a typedef. *)

val get_class_name_from_pointer: env -> typ -> (qualified_name * tkind)
(** [get_class_name_from_pointer env ty] returns the name of the class [ty]
    points to, unrolling typedefs if needed. *)

val get_class_name_from_reference: env -> typ -> (qualified_name * tkind * bool)
(** [get_class_name_from_reference env ty] returns the name of the class [ty]
    is bound to, either directly (returned boolean flag is [false] or through
    a reference (returned flag is [true]). Typedefs are unrolled as needed. *)

val get_struct_name: env -> typ -> (qualified_name * tkind)
(** get the name of the given aggregate (or pointer/ref to aggregate) type 
    unfold typedef if needed. *)

val get_signature_type: env -> typ -> signature
 (** get the signature of the given functional type. *)

val get_struct_name_exp: env -> exp_node -> (qualified_name * tkind)
(** get the name of the aggregate type of the given object. *)

val get_dynamic_signature: env -> exp_node -> signature
 (** gets the dynamic type of the given expression. *)

val closure_var_kind: env -> string -> bool option
 (** [Some is_ref] if the given string
     (that may be "this") is a captured identifier,
     where [is_ref] is true iff the capture is done by reference.
     [None] otherwise. *)

val reset_closure: env -> env
  (** remove information about captured identifiers. *)

val add_closure_info: env -> capture list -> env
  (** Associates the given identifiers to the appropriate closure kind. *)
