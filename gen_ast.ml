(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-Clang                                      *)
(*                                                                        *)
(*  Copyright (C) 2012-2018                                               *)
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

open Genlex

type pretty_field =
  | Named of string
  | Anonymous of int

type pretty_arg =
  | Pretty of pretty_field
  | Normal of pretty_field

type pretty = string * pretty_arg list

type typ =
  | Bool
  | Int
  | Int64
  | Location
  | String
  | Node of string
  | Option of typ
  | List of typ

type args = (string * typ) list

type constructor = string * args * pretty

type nodes =
  | Union of constructor list
  | Nuple of args * pretty

type type_def =
  { name: string; definition: nodes;
    ml_norm: (string * string) option; c_norm: (string * string) option;
  }

type ast = (string * nodes) list

let lexer =
  Genlex.make_lexer
    [ "bool"; "int"; "int64"; "list"; "location"; "option";
      "pretty"; "string"; "type"; "normalize"; "C"; "OCaml";
       "`"; "|"; "{"; "}"; "("; ")"; ";" ; ":"; "*"; "=";
    ]

let mk_typ name definition norms =
  let c_norm = List.assoc_opt "C" norms in
  let ml_norm = List.assoc_opt "OCaml" norms in
  { name; definition; c_norm; ml_norm }

let end_command = parser [< 'Kwd ";"; 'Kwd ";" >] -> ()

let rec parse_ast = parser
  | [< 'Kwd "type"; 'Ident n; 'Kwd "="; def = parse_nodes;
       norms = parse_normalization; _ = end_command;
       tl = parse_ast; >] -> (mk_typ n def norms)::tl
  | [< >] -> []
and parse_nodes = parser
  | [< f=parse_fields; pretty = parse_pretty >] -> Nuple (f,pretty)
  | [< cons = parse_constructors >] ->
      Union cons
and parse_constructors = parser
  | [< 'Kwd "|"; 'Ident c; f = parse_fields;
       p=parse_pretty; tl = parse_constructors >] -> (c,f,p) :: tl
  | [< >] -> []
and parse_type = parser
  | [< t = parse_basic_type; m = parse_modifier >] -> m t
and parse_basic_type = parser
  | [< 'Ident t >] -> Node t
  | [< 'Kwd "bool" >] -> Bool
  | [< 'Kwd "int" >] -> Int
  | [< 'Kwd "int64" >] -> Int64
  | [< 'Kwd "location" >] -> Location
  | [< 'Kwd "string" >] -> String
(*   | [< 'Kwd "("; t = parse_type; 'Kwd ")" >] -> t *)
and parse_modifier = parser
  | [< 'Kwd "list"; f = parse_modifier >] -> fun t -> f (List t)
  | [< 'Kwd "option"; f = parse_modifier >] -> fun t -> f (Option t)
  | [< >]  -> fun t -> t
and parse_pretty = parser
  | [< 'Kwd "pretty"; 'Genlex.String s; args = parse_pretty_args >] -> s, args
  | [< >] -> "",[]
and parse_pretty_args = parser
  | [< 'Kwd "pretty"; a = parse_arg_name; tl = parse_pretty_args >] ->
      (Pretty a)::tl
  | [< a = parse_arg_name; tl = parse_pretty_args >] ->
      (Normal a)::tl
and parse_arg_name = parser
  | [< 'Genlex.String s >] -> Named s
  | [< 'Genlex.Int n >] -> Anonymous n

and parse_normalization = parser
  | [< 'Kwd "OCaml";
       body = parse_normalization_body; l = parse_normalization >] ->
    ("OCaml", body) :: l
  | [< 'Kwd "C"; body = parse_normalization_body; l = parse_normalization >] ->
    ("C", body) :: l
  | [< >] -> []

and parse_normalization_body = parser
  | [< 'Kwd "normalize";
       'Ident arg; 'Kwd "="; 'Genlex.String body; >] -> (arg, body)

and parse_fields = parser
  | [< 'Kwd "{"; l = field_list; 'Kwd "}" >] -> l
and field_list = parser
  | [< hd = parse_field; 'Kwd ";"; tl = field_list >] -> hd::tl
  | [< >] -> []
and parse_field = parser
  | [< 'Ident c; 'Kwd ":"; ty = parse_type >] -> c,ty

let pretty_list
    ?(pre=format_of_string "") 
    ?(sep=format_of_string "@ ")
    ?(suf=format_of_string "") pretty fmt =
  function
    | [] -> ()
    | x::tl ->
        let rec aux fmt =
          function
            | [] -> ()
            | x :: tl -> Format.fprintf fmt (sep ^^ "%a%a") pretty x aux tl
        in
        Format.fprintf fmt (pre ^^ "%a%a" ^^ suf) pretty x aux tl

let rec print_ocaml_type fmt =
  function
    | Bool -> Format.fprintf fmt "bool"
    | Int -> Format.fprintf fmt "int"
    | Int64 -> Format.fprintf fmt "Int64.t"
    | Location -> Format.fprintf fmt "location"
    | String -> Format.fprintf fmt "string"
    | Node s ->
      Format.pp_print_string fmt (String.uncapitalize_ascii s)
    | Option t -> Format.fprintf fmt "(@[%a@])@ option" print_ocaml_type t
    | List t -> Format.fprintf fmt "(@[%a@])@ list" print_ocaml_type t

module String_set = Set.Make(String)

let duplicated_fields = ref String_set.empty

let known_fields = ref String_set.empty

let add_field c =
  if String_set.mem c !known_fields then
    duplicated_fields := String_set.add c !duplicated_fields
  else
    known_fields:=String_set.add c !known_fields

let disambiguate_field type_name n =
  if String_set.mem n !duplicated_fields then type_name ^ "_" ^ n else n

let print_ocaml_field type_name fmt (n,t) =
  Format.fprintf fmt "%s: %a"
    (disambiguate_field type_name n) print_ocaml_type t

(* defining OCaml types *)
let print_ocaml_typedef kw fmt { name = s; definition = t } =
  let print_body fmt =
    function
      | Union c ->
          List.iter
            (fun (name,args,_) ->
              Format.fprintf fmt "| @[%s%a@]@;"
                (String.capitalize_ascii name)
                (pretty_list ~pre:" of@ " ~sep:"@ *@ "
                   (fun fmt (_,t) -> print_ocaml_type fmt t))
                args)
            c
      | Nuple (t,_) ->
          Format.fprintf fmt "{@[<v 2> %a@]@;}@;"
          (pretty_list ~sep:";@;" (print_ocaml_field s)) t
  in
  Format.fprintf fmt "@[<v 2>%s %s =@;%a@]@;"
    kw (String.uncapitalize_ascii s) print_body t

let check_duplicate t =
  match t.definition with
  | Union _ -> () (* TODO: check for duplicated constructors *)
  | Nuple (t,_) -> List.iter (fun (n,_) -> add_field n) t

let check_duplicates ast = List.iter check_duplicate ast

let generate_ocaml_ast fmt ast =
  match ast with
    | [] -> ()
    | t1 :: tl ->
        Format.pp_open_vbox fmt 0;
        print_ocaml_typedef "type" fmt t1;
        List.iter (print_ocaml_typedef "and" fmt) tl;
        Format.pp_close_box fmt ()

let rec parse_typ msg arg fmt typ =
  match typ with
    | Bool ->
        Format.fprintf fmt
          "@[<v 2>match %s.value with@;| VTrue -> true @;| VFalse -> false@;\
           | _ -> parse_error %S %s@]" arg msg arg
    | Int ->
        Format.fprintf fmt
          "@[<v 2>match %s.value with@;| VInt n -> Int64.to_int n @;\
           | _ -> parse_error %S %s@]" arg msg arg
    | Int64 ->
        Format.fprintf fmt
          "@[<v 2>match %s.value with@;| VInt n -> n @;\
           | _ -> parse_error %S %s@]" arg msg arg
    | Location -> Format.fprintf fmt "parse_location %s" arg
    | String ->
        Format.fprintf fmt
          "@[<v 2>match %s.value with@;| VString s -> s@;\
           | _ -> parse_error %S %s@]" arg msg arg
    | Node s -> Format.fprintf fmt "parse_%s %s" s arg
    | Option t ->
        Format.fprintf fmt
          "@[<v 2>match %s.value with@;| VNone -> None @;\
           @[<v 2>| _ ->@;@[<hov 2>Some(@;%a)@]@]@]" 
          arg (parse_typ msg arg) t
    | List t ->
        Format.fprintf fmt
           "@[<v 2>match %s.value with@;| VNil -> [] @;\
            @[<v 2>| VName \"Cons\" ->@;\
            @[<v 2>List.map@;@[<hov 2>(fun %s -> %a)@]@;%s.children@]@;\
             | _ -> parse_error \"Expecting a list\" %s@]"
          arg arg (parse_typ msg arg) t arg arg
          

let generate_child parent_name fmt final_name (name, typ) =
  Format.fprintf fmt
    "@[<v 2>let __node =@;try List.hd children@;\
     with Failure _ -> \
     parse_error \"No node for child %s of %s\" __node@]@;in@;\
     @[<v 2>let %s =@;%a@]@;in"
    name parent_name final_name
    (parse_typ ("Expecting child " ^ name ^ " of " ^ parent_name) "__node")
    typ

let generate_field_child parent_name fmt (name,_ as field) =
  generate_child parent_name fmt (disambiguate_field parent_name name) field

let generate_constructor_child parent_name fmt (name,_ as field) =
  generate_child parent_name fmt name field

let generate_field_node type_name fmt (name,_) = 
  Format.pp_print_string fmt (disambiguate_field type_name name)

let generate_constructor_node fmt (name,_) =
  Format.pp_print_string fmt name

(*
let generate_nuple_children () =
  let i = ref 0 in
  fun fmt typ ->
    generate_child fmt ("field" ^ (string_of_int !i)) typ; incr i

let generate_nuple_node () =
  let i = ref 0 in
  fun fmt _ -> Format.fprintf fmt "field%d" !i; incr i
*)

let generate_union_parser name fmt (cons,args,_) =
  Format.fprintf fmt 
    "@[<hv 2>| VName \"%s\" ->@ %a@ @[<hov 2>%s@;%a@]@]@;"
    cons
    (* There is a guarded List.hd just before, no need to catch an exn. *)
    (pretty_list
       ~sep:"@;let children = List.tl children in@;"
       (generate_constructor_child name))
    args
    (String.capitalize_ascii cons)
    (pretty_list ~pre:"(" ~sep:",@ " ~suf:")" generate_constructor_node) args

let pretty_norm_arg fmt norm =
  match norm with None -> () | Some (a, _) -> Format.fprintf fmt "let %s=@;" a

let pretty_norm_body fmt norm =
  match norm with None -> () | Some (_,b) -> Format.fprintf fmt "in@;%s@;" b

let generate_type_parser fmt { name; definition; ml_norm } =
  match definition with
    | Union l ->
        Format.fprintf fmt
          "parse_%s __node=@;\
          @[<v 2>%a%tmatch __node.value with@;%a@;\
          @[<v 2>| VName _ ->@;\
          parse_error \"Unknown constructor for %s\" __node@]@;
          | _ -> parse_error \"Expecting constructor of %s\" __node@]%a"
          name
          pretty_norm_arg ml_norm
          (fun fmt ->
            if List.exists (fun (_,l,_) -> l <>[]) l then
              Format.fprintf fmt "let children = __node.children in@;")
          (pretty_list
             ~sep:"@;"
             (generate_union_parser name))
          l
          name
          name
          pretty_norm_body ml_norm
    | Nuple (l, _) ->
        Format.fprintf fmt
          "@[<v 2>parse_%s __node=@;%a@;\
           let children = __node.children in@;%a@;%a@]%a"
          name
          pretty_norm_arg ml_norm
          (pretty_list
             ~sep:"@;let children = List.tl children in@;"
             (generate_field_child name))
          l
          (pretty_list ~pre:"{@[<hov 2>" ~sep:";@ " ~suf:"@]}@;"
             (generate_field_node name))
          l
          pretty_norm_body ml_norm

let generate_parse_fun_sig fmt { name } =
  Format.fprintf fmt "val parse_%s:@ tree ->@ %s" name name

let generate_ocaml_parser_sig fmt base ast =
  Format.fprintf fmt
    "@[<v 0>open %s@;@;type tree@;@;\
     val make_tree: in_channel->tree@;\
     val print_tree: Format.formatter -> tree -> unit@;@;\
     exception Parse_error of string@;@;%a@]"
    (String.capitalize_ascii (Filename.basename base))
    (pretty_list ~pre:"@[<hov 2>" ~sep:"@]@;@;@[<hov 2>" ~suf:"@]"
       generate_parse_fun_sig) ast

let pretty_recursive f fmt l =
  pretty_list ~pre:"@[<v 2>let rec " ~sep:"@]@;@[<v 2>and "
    ~suf:"@]@;@;" f fmt l

let generate_ocaml_parser_impl fmt base ast =
  Format.fprintf fmt
    "@[<v 0>open %s@;@[<v 2>type value =@;\
     | VNil | VNone | VTrue | VFalse | VString of string | VInt of Int64.t \
     | VName of string@]@;@;\
     type tree = { value: value; line: int; mutable children: tree list }@;@;\
     @[<v 2>let print_value out = function@;\
     | VNil -> Format.fprintf out \"nil\"@;\
     | VNone -> Format.fprintf out \"none\"@;\
     | VTrue -> Format.fprintf out \"true\"@;\
     | VFalse -> Format.fprintf out \"false\"@;\
     | VString s -> Format.fprintf out \"%%S\" s@;\
     | VInt n -> Format.fprintf out \"%%s\" (Int64.to_string n)@;\
     | VName s -> Format.fprintf out \"%%s\" s@]@;@;\
     @[<v 2>let print_tree out t =@;\
     @[<v 2>let rec aux i t =@;\
     Format.fprintf out \"%%*s%%a@@\\n\" i \"\" print_value t.value;@;\
     List.iter (aux (i+2)) t.children;@]@;\
     in aux 0 t@]@;@;\ 
     @[<v 2>let make_tree chan =@;\
     let parents = ref \
     [ { value = VName \"root\"; line = 0; children = [] } ] in@;\
     let indent = ref (-2) in@;\
     let nb_lines = ref 0 in@;\
     let ib = Scanf.Scanning.from_channel chan in@;\
     @[<v 2>try@;@[<v 2>while true do@;\
     incr nb_lines;@;\
     let (b,e,s) = Scanf.bscanf ib \"%%n %%n%%[^\\n]\\n\"\
     (fun b e s -> (b,e,s)) in@;\
     let n = e - b in@;\
     @[<v 2>let value =@;\
     if s = \"nil\" then VNil@;\
     else if s = \"true\" then VTrue@;\
     else if s = \"false\" then VFalse@;\
     else if s = \"none\" then VNone@;\
     else try VInt (Int64.of_string s)@;\
     @[<v 2>with Failure _ ->@;\
     @[<v 2>if s.[0] = '\"' then begin@;\
     let s = String.sub s 1 (String.length s - 1) in@;\
     let b = Buffer.create 15 in@;\
     @[<v 2>if String.length s = 0 || s.[String.length s - 1] <> '\"';\
     then begin@;\
     Buffer.add_string b s;@;\
     @[<v 2>try while true do@;\
     let s = Scanf.bscanf ib \"%%[^\\n]\\n\" (fun s -> s) in@;\
     Buffer.add_char b '\\n';@;\
     @[<v 2>if String.length s = 0 || s.[String.length s - 1] <> '\"';\
     then@;Buffer.add_string b s@]@;@[<v 2>else begin@;\
     Buffer.add_string b (String.sub s 0 (String.length s - 1));@;\
     raise Exit;@]@;\
     end;@]@;\
     done;@;\
     with Exit -> ()@]@;\
     end else Buffer.add_string b (String.sub s 0 (String.length s - 1));@;\
     VString (Buffer.contents b)@]@;\
     end else VName s@]@]@;in@;\
     let __node = { value = value; children = []; line = !nb_lines } in@;\
     @[<v 2>while n <= !indent do@;\
     indent := !indent - 2;@;\
     @[<v 2>let __node =@;\
     try List.hd !parents with@;\
     @[<v 2>Failure _ ->@;\
     @[<v 2>failwith (@;\"empty list of parents for node \" ^ s@;\
     ^ \" at line \" ^ (string_of_int !nb_lines))@]@]@]@;\
     in __node.children <- List.rev __node.children;@;\
     parents:=List.tl !parents;@]@;done;@;\
     indent:=n;@;\
     @[<v 2>let parent =@;try List.hd !parents with@;\
     @[<v 2>Failure _ ->@;\
     @[<v 2>failwith (@;\"empty list of parents for node \" ^ s@;\
     ^ \" at line \" ^ (string_of_int !nb_lines))@]@]@]@;\
     in@;\
     parent.children <- __node :: parent.children;@;\
     parents:=__node::!parents;\
     @]@;done;@;assert false;@]@;\
     @[<v 2>with End_of_file ->@;
     List.iter (fun n -> n.children <- List.rev n.children) !parents;@;
     List.hd (List.hd (List.rev !parents)).children@]@]@;@;\
     exception Parse_error of string@;\
     @[<v 2>let parse_error msg __node =@;\
        let s = Format.asprintf \"@@[line %%d: unexpected %%a (%%s)@@]@@.\"@;\
          __node.line print_value __node.value msg@;\
        in@;\
        raise (Parse_error s)@]@;@;\
     @[<v 2>let parse_location __node =@;\
     @[<v 2>match __node.children with@;\
     @[<v 2>| [file1;line1;char1;file2;line2;char2] ->@;\
     @[<v 2>let file1 =@;\
     @[<v 2>match file1.value with VString s -> s @;\
     | _ -> parse_error \"expecting file name\" file1@]@]@;in@;\
     @[<v 2>let line1 =@;\
     @[<v 2>match line1.value with VInt d -> Int64.to_int d@;\
     | _ -> parse_error \"expecting line number\" line1@]@]@;in@;\
     @[<v 2>let char1 =@;\
     @[<v 2>match char1.value with VInt d -> Int64.to_int d@;\
     | _ -> parse_error \"expecting column number\" char1@]@]@;in@;\
     @[<v 2>let file2 =@;\
     @[<v 2>match file2.value with VString s -> s@;\
     | _ -> parse_error \"expecting file name\" file2@]@]@;in@;\
     @[<v 2>let line2 =@;\
     @[<v 2>match line2.value with VInt d -> Int64.to_int d@;\
     | _ -> parse_error \"expecting line number\" line2@]@]@;in@;\
     @[<v 2>let char2 =@;\
     @[<v 2>match char2.value with VInt d -> Int64.to_int d@;\
     | _ -> parse_error \"expecting column number\" char2@]@]@;in@;\
     @[<v 2>@[<v 3>({@;Lexing.pos_fname = file1;@;pos_lnum = line1;@;\
     pos_bol = 0;@;pos_cnum = char1},@]@;@[<v 1>{@;\
     Lexing.pos_fname = file2;@;pos_lnum = line2;@;\
     pos_bol = 0;@;pos_cnum = char2})@]@]@;\
     | _ -> parse_error \"expecting a location\" __node@]@]@]@;@;\
     %a@]"
    (String.capitalize_ascii (Filename.basename base))
    (pretty_recursive generate_type_parser) ast

let generate_rank fmt l =
  List.fold_left
    (fun r (s,l,_) ->
      let print_arg fmt =
        match l with [] -> () | _ -> Format.pp_print_string fmt " _"
      in
      Format.fprintf fmt "| %s%t -> %d@;" s print_arg r;
      r+1)
    0 l

type chan_fmt = { channel: out_channel; fmt: Format.formatter }

let create_chan_fmt name =
  let channel = open_out name in
  let fmt = Format.formatter_of_out_channel channel in
  { channel = channel; fmt = fmt }

let create_ml_mli base =
  let mlfile = base ^ ".ml" in
  let mlifile = base ^ ".mli" in
  create_chan_fmt mlfile, create_chan_fmt mlifile

let flush_and_close chfmt =
  Format.pp_print_flush chfmt.fmt (); close_out chfmt.channel

let generate_ocaml_type base ast =
  let mli = create_chan_fmt (base ^ ".mli") in
  check_duplicates ast;
  Format.fprintf mli.fmt
    "@[<v 0>type location = Lexing.position * Lexing.position@;@;@]";
  generate_ocaml_ast mli.fmt ast;
  flush_and_close mli

let generate_ocaml_parser base ast =
  let ml, mli = create_ml_mli (base ^ "_parser") in
  generate_ocaml_parser_impl ml.fmt base ast;
  generate_ocaml_parser_sig mli.fmt base ast;
  flush_and_close ml; flush_and_close mli

let generate_ocaml_file s ast =
  try
    let base = Filename.chop_extension s in
    generate_ocaml_type base ast;
    generate_ocaml_parser base ast;
  with Sys_error e ->
    Printf.eprintf "Unable to generate OCaml bindings: %s\n%!" e

(* defining C types *)
let has_only_const_constructors l =
  List.for_all (function (_,[],_) -> true | (_,_,_) -> false) l

let type_table = Hashtbl.create 13

let fill_type_table ast =
  List.iter
    (function
      | { name; definition = Nuple _} -> Hashtbl.add type_table name false
      | { name; definition = Union l} ->
        Hashtbl.add type_table name (has_only_const_constructors l))
    ast

let is_base_type = function
  | Bool | Int | Int64 -> true
  | Node s ->
    (try Hashtbl.find type_table s
     with Not_found ->
       Printf.eprintf "Type %s is used but not defined" s; exit 2)
  | Location | String | Option _ | List _ -> false

let print_c_type fmt = function
  | Bool -> Format.pp_print_string fmt "bool"
  | Int -> Format.pp_print_string fmt "int32_t" 
    (* should be int31_t for complete compatibility with OCaml, but this is
       seldom defined. *)
  | Int64 -> Format.pp_print_string fmt "int64_t"
  | Location -> Format.pp_print_string fmt "location"
  | String -> Format.pp_print_string fmt "const char *"
  | Node s -> Format.pp_print_string fmt s
  | Option _ -> Format.pp_print_string fmt "option" (* not very typesafe *)
  | List _ -> Format.pp_print_string fmt "list" (* not very typesafe *)

let generate_tag fmt (name,_,_) =
  Format.pp_print_string fmt (String.uppercase_ascii name)

let generate_enum_decl fmt { name; definition } =
  match definition with
    | Union l ->
        Format.fprintf fmt "@[<hov 2>enum tag_%s {@ %a@;};@]@;"
          name (pretty_list ~sep:",@ " generate_tag) l;
    | Nuple _ -> ()

let generate_typedef fmt { name; definition } =
  match definition with
    | Union l when has_only_const_constructors l ->
        Format.fprintf fmt "@[<hov 2>typedef@ enum tag_%s@ %s;@;@]" name name
    | Nuple _ | Union _ ->
        Format.fprintf fmt "@[<hov 2>typedef@ struct _%s@ *%s@;;@]" name name

let generate_union_case_args fmt (name,t) =
  Format.fprintf fmt "@[<hov 2>%a@ %s;@]" print_c_type t name

let generate_union_case fmt (name,args,_) =
  match args with
    | [] -> () (* for constant constructors, we don't need to have
                  anything beyond the tag. *)
    | _ ->
        Format.fprintf fmt "@[<v 2>struct {@;%a@;} %s;@]"
          (pretty_list ~sep:"@;" generate_union_case_args) args name

let generate_struct_fields fmt (n,t) =
  Format.fprintf fmt "@[<hov 2>%a %s;@ @]" print_c_type t n

let generate_discriminated_union fmt { name; definition } =
  match definition with
    | Union l ->
        if not (has_only_const_constructors l) then begin
          Format.fprintf fmt
            "@[<v 2>struct _%s {@;@[<hov 2>enum tag_%s tag_%s;@]@;\
             @[<v 2>union {@;%a@;} cons_%s;@]@;};@]"
            name name name
            (pretty_list ~sep:"@;" generate_union_case) l
            name
        end
    | Nuple (l,_) ->
        Format.fprintf fmt "@[<v 2>struct _%s {@;%a@]@;};" name
          (pretty_list ~sep:"@;" generate_struct_fields) l

let generate_proto_arg_named fmt (name, typ) =
  Format.fprintf fmt "%a@ %s" print_c_type typ name

let generate_non_null_assert fmt (name, typ) =
  match typ with
  | Bool | Int | Int64 | List _ | String -> ()
  (* empty list is denoted by NULL, and strings can be NULL to denote empty
     string. *)
  | Location | Option _ -> Format.fprintf fmt "assert(%s);@\n" name
  | Node s -> (* only if not an enumerated type. *)
    if not (Hashtbl.find type_table s) then
      Format.fprintf fmt "assert(%s);@\n" name

let generate_cons_proto_union name fmt (cons,prm,_) =
  Format.fprintf fmt
    "@[<hov 2>%s@ %s_%s(%a);@]" name name cons
    (pretty_list ~pre:"@;" ~sep:",@ " ~suf:"@;" generate_proto_arg_named) prm

let generate_cons_union name norm fmt (cons,prm,_) =
  let assign_field fmt (prm, _) =
    Format.fprintf fmt "obj->cons_%s.%s.%s = %s;" name cons prm prm
  in
  let obj, norm =
    match norm with
    | None -> "obj", ""
    | Some (obj, norm) -> obj, norm
  in
  Format.fprintf fmt
    "@[<v 2>@[<hov 2>%s@ %s_%s(%a)@ {@]@;\
     %a\
     %s%s %s = NULL;@;%t%s = malloc(sizeof(*%s));@;\
     @[<v 2>if(%s){@;%s->tag_%s=%s;%a@]@;}@;%t%s@;return %s;@]@;}"
    name name cons
    (pretty_list ~pre:"@;" ~sep:",@ " ~suf:"@;" generate_proto_arg_named) prm
    (pretty_list ~sep:"" generate_non_null_assert) prm
    ((* if prm = [] then "static " else *) "") (* see free *)
    name obj
    (fun fmt -> if prm = [] then Format.fprintf fmt "@[<v 2>if (!%s) {@;" obj)
    obj obj obj obj
    name (String.uppercase_ascii cons)
    (pretty_list ~sep:"@;" assign_field) prm
    (fun fmt -> if prm = [] then Format.fprintf fmt "@]@;}@;")
    norm obj

let generate_cons_proto_nuple name fmt prm =
  Format.fprintf fmt
    "@[<hov 2>%s@ %s_cons(%a);@]" name name
    (pretty_list ~pre:"@;" ~sep:",@ " ~suf:"@;" generate_proto_arg_named) prm

let generate_cons_nuple name norm fmt prm =
  let obj, norm =
    match norm with
    | None -> "obj", ""
    | Some (obj, norm) -> obj, norm
  in
  let print_prm fmt (n, typ) =
    Format.fprintf fmt "%a %s" print_c_type typ n
  in
  let assign_field fmt (n,_) =
    Format.fprintf fmt "obj->%s = %s;" n n
  in
  Format.fprintf fmt
    "@[<v 2>@[<hov 2>%s@ %s_cons(%a) {@]@;\
       %a\
       %s %s = malloc(sizeof(*%s));@;\
       @[<v 2>if (%s) {@;%a@]@;}@;%s@;return %s;@]@;}"
    name name
    (pretty_list ~pre:"@;" ~sep:",@ " ~suf:"@;" print_prm) prm
    (pretty_list generate_non_null_assert) prm
    name obj obj obj
    (pretty_list ~sep:"@;" assign_field) prm
    norm obj

let generate_constructor_proto fmt { name; definition } =
  let pretty_list_newline f l =
    pretty_list ~pre:"@[<v 0>" ~sep:"@;" ~suf:"@;@]" f fmt l
  in
  match definition with
    | Union l when has_only_const_constructors l -> ()
        (* only represented by an enum: no need for specific constructors. *)
    | Union l -> pretty_list_newline (generate_cons_proto_union name) l
    | Nuple (l,_) -> generate_cons_proto_nuple name fmt l

let generate_destructor_proto fmt { name } =
  Format.fprintf fmt "@[void free_%s(%s);@]" name name

let generate_dup_proto fmt { name } =
  Format.fprintf fmt "@[%s %s_dup(const %s);@]" name name name

let generate_equal_proto fmt { name } =
  Format.fprintf fmt "@[bool %s_equal(const %s, const %s);@]" name name name

let generate_c_ast fmt ast =
  let pretty_list_newline f = pretty_list ~sep:"@;" ~suf:"@;" f in
  Format.fprintf fmt "@[<v 0>%a%a@;%a@;%a@;%a%a%a@]"
    (pretty_list ~sep:"" generate_enum_decl) ast
    (pretty_list_newline generate_typedef) ast
    (pretty_list_newline generate_discriminated_union) ast
    (pretty_list_newline generate_constructor_proto) ast
    (pretty_list_newline generate_destructor_proto) ast
    (pretty_list_newline generate_dup_proto) ast
    (pretty_list_newline generate_equal_proto) ast

let generate_constructor fmt { name; definition; c_norm } =
  match definition with
    | Union l when has_only_const_constructors l -> ()
    | Union l ->
        pretty_list ~sep:"@;@;" (generate_cons_union name c_norm) fmt l
    | Nuple(l,_) -> generate_cons_nuple name c_norm fmt l

let generate_c_constructor fmt ast =
  pretty_list ~pre:"@[<v 0>" ~sep:"@;@;" ~suf:"@;@;@]"
    generate_constructor fmt ast

let rec generate_free_call obj fmt t =
  match t with
    | Bool | Int | Int64 -> ()
    | Location -> Format.fprintf fmt "free_location(%t);@;" obj
    | String -> () (* as we don't use strdup, we cannot assume that
                      we own those strings (in fact, they are very likely to
                      come straight from clang)
                   *)
    | Node s -> Format.fprintf fmt "free_%s(%t);@;" s obj
    | Option t ->
      let subobj fmt = Format.fprintf fmt "%t->content" obj in
      Format.fprintf fmt "@[<v 2>if(%t->is_some) {@;%a@]@;}@;free(%t);"
        obj (destruct_ptr_or_int subobj) t obj
    | List t ->
      Format.fprintf fmt
        "@[<v 2>{ list elt = %t;@;\
         @[<v 2>while(elt) {@;\
         list tmp=elt->next;@;%a@;free(elt);@;elt=tmp;@]@;}@]@;}"
        obj
        (destruct_ptr_or_int
           (fun fmt -> Format.pp_print_string fmt "elt->element"))
        t
and destruct_ptr_or_int obj fmt t =
  if not (is_base_type t) then begin
    let content fmt = Format.pp_print_string fmt "content" in
    Format.fprintf fmt
      "%a content = (%a)%t.container;@;%a"
      print_c_type t
      print_c_type t
      obj
      (generate_free_call content) t
  end
 

let generate_destructor_body obj fmt (name,typ) =
  let obj fmt = Format.fprintf fmt "%t.%s" obj name in
  generate_free_call obj fmt typ

let generate_destructor_case name fmt (cons,args,_) =
  let obj fmt = Format.fprintf fmt "obj->cons_%s.%s" name cons in
  Format.fprintf fmt "@[<v 2>case %s:@;%abreak;@]@;"
    (String.uppercase_ascii cons)
    (pretty_list (generate_destructor_body obj)) args

let generate_destructor_nuple fmt args =
  let obj fmt = Format.pp_print_string fmt "(*obj)" in
  pretty_list (generate_destructor_body obj) fmt args

let generate_destructor fmt { name; definition } =
  match definition with
    | Union l when has_only_const_constructors l ->
        Format.fprintf fmt "@[void free_%s(%s obj) { }@]@;" name name
        (* only here to allow for an uniform treatment of destructors 
           (otherwise, we have to keep an environment of types in order
           not to call free_name when we have an argument of type name)
        *)
    | Union l ->
        Format.fprintf fmt 
          "@[<v 2>void free_%s(%s obj) {@;\
           if (!obj) return;@;
           @[<v 2>switch (obj -> tag_%s) {@;%a@]@;}@;
           free(obj);@]@;}"
          name name name
          (pretty_list (generate_destructor_case name)) l
    | Nuple (l,_) ->
        Format.fprintf fmt
          "@[<v 2>void free_%s(%s obj){@;\
           if(!obj) return;@;%a@;free(obj);@]@;}"
          name name generate_destructor_nuple l

let rec generate_dup_assigns dst src fmt = function
    | Bool | Int | Int64 -> Format.fprintf fmt "%t = %t;@;" dst src
    | Location -> 
      Format.fprintf fmt
        "%t = copy_loc(%t);@;" dst src
    | String -> Format.fprintf fmt
       "%t=strdup(%t);@;if(%t==NULL) memory_exhausted();@;" dst src dst
    | Node s -> Format.fprintf fmt "%t = %s_dup(%t);@;" dst s src
    | Option t ->
      let subobj obj fmt = Format.fprintf fmt "%t->content" obj in
      Format.fprintf fmt 
        "%t = malloc(sizeof(struct _option));@;\
         %t->is_some = %t->is_some;@;\
         @[<v 2>if(%t->is_some) {@;%a@]@;}@;"
        dst dst src src (dup_opt_ptr_or_int (subobj dst) (subobj src)) t
    | List t ->
      Format.fprintf fmt
        "@[<v 2>{@;\
         list elt_src = %t;@;\
         %t = NULL;@;\
         list elt_dst = NULL;@;\         
         @[<v 2>while(elt_src) {@;\
         list tmp = malloc(sizeof(struct _list));@;\
         if (!tmp) { memory_exhausted(); };@;\
         %a@;tmp->next=NULL;@;\
         @[<v 2>if(elt_dst) {@;\
         elt_dst->next = tmp;@;\
         @]@;@[<v 2>} else {@;\
         %t=tmp;@;\
         @]@;}@;\
         elt_dst=tmp;@;\
         elt_src=elt_src->next;@]@;}@;@]}@;"
        src dst
        dup_list_ptr_or_int t
        dst
and dup_opt_ptr_or_int dst src fmt t =
  let src fmt =
    if is_base_type t then
      Format.fprintf fmt "%t.plain" src
    else
      Format.fprintf fmt "(%a)%t.container"
      print_c_type t src
  in
  let dst fmt = Format.fprintf fmt "%t.%s" dst
    (if is_base_type t then "plain" else "container")
  in
  generate_dup_assigns dst src fmt t

and dup_list_ptr_or_int fmt t =
  let dst fmt =
    if is_base_type t then Format.pp_print_string fmt "tmp->element.plain"
    else
      Format.fprintf fmt "tmp->element.container"
  in
  let src fmt =
    if is_base_type t then Format.pp_print_string fmt "elt_src->element.plain"
    else
      Format.fprintf fmt "(%a)elt_src->element.container" print_c_type t
  in
  generate_dup_assigns dst src fmt t

let generate_dup_body dst src fmt (name,typ) =
  let src fmt = Format.fprintf fmt "%t.%s" src name in
  let dst fmt = Format.fprintf fmt "%t.%s" dst name in
  generate_dup_assigns dst src fmt typ

let generate_dup_union_args name cons_name fmt =
  let src fmt = Format.fprintf fmt "src->cons_%s.%s" name cons_name in
  let dst fmt = Format.fprintf fmt "dst->cons_%s.%s" name cons_name in
  generate_dup_body dst src fmt

let generate_dup_case name fmt (cons,args,_) =
  Format.fprintf fmt 
    "@[<v 2>case %s: {@;%a@;break;@;@]}"
    (String.uppercase_ascii cons)
    (pretty_list ~sep:"@;" (generate_dup_union_args name cons)) args

let generate_dup_nuple fmt l =
  let src fmt = Format.pp_print_string fmt "(*src)" in
  let dst fmt = Format.pp_print_string fmt "(*dst)" in
  pretty_list (generate_dup_body dst src) fmt l

let generate_dup fmt { name; definition } =
  match definition with
    | Union l when has_only_const_constructors l ->
      Format.fprintf fmt "%s %s_dup(const %s x) { return x; }" name name name
    | Union l ->
      Format.fprintf fmt
        "@[<v 2>%s %s_dup(const %s src) {@;\
         if (src == NULL) return NULL;@;\
         %s dst = malloc(sizeof(*src));@;\
         if(dst == NULL) memory_exhausted();@;\
         dst->tag_%s = src->tag_%s;@;\
         @[<v 2>switch (src->tag_%s) {@;\
         %a\
         @]@;}@;\
         return dst;\
         @]@;}"
        name name name name name name name
        (pretty_list (generate_dup_case name)) l
    | Nuple(l,_) ->
      Format.fprintf fmt
        "@[<v 2>%s %s_dup(const %s src) {@;\
         if (src == NULL) return NULL;@;\
         %s dst = malloc(sizeof(*src));@;\
         if (dst == NULL) memory_exhausted();@;\
         %a\
         return dst;\
         @]@;}"
        name name name name
        generate_dup_nuple l

let ptr_or_int fmt t v =
  if is_base_type t then
    Format.fprintf fmt "%t.plain" v
  else
    Format.fprintf fmt "(%a)%t.container" print_c_type t v

let rec generate_eq_type v1 v2 fmt =
  function
    | Bool | Int | Int64 ->
      Format.fprintf fmt "if (%t != %t) return false;@;" v1 v2
    | Location -> () (* we don't discriminate wrt locations *)
    | String ->
      Format.fprintf fmt "if (strcmp(%t,%t) != 0) return false;@;" v1 v2
    | Node s ->
      Format.fprintf fmt "if (!%s_equal(%t,%t)) return false;@;" s v1 v2
    | Option t ->
      let field v fmt =
        let subobj fmt = Format.fprintf fmt "%t->content" v in
        ptr_or_int fmt t subobj
      in
      let sub_v1 fmt = field v1 fmt in
      let sub_v2 fmt = field v2 fmt in
      Format.fprintf fmt
      "if (%t->is_some != %t->is_some) return false;@;\
       @[<v 2>if (%t->is_some) {@;%a@]@;}@;"
        v1 v2 v1 (generate_eq_type sub_v1 sub_v2) t
    | List t ->
      let field s fmt =
        let subobj fmt = Format.fprintf fmt "%s->element" s in
        ptr_or_int fmt t subobj
      in
      let sub_v1 fmt = field "l1" fmt in
      let sub_v2 fmt = field "l2" fmt in
      Format.fprintf fmt
        "@[<v 2>{@;list l1 = %t, l2 = %t;@;\
         @[<v 2>while (true) {@;\
         if (l1 == NULL && l2 == NULL) break;@;
         if (l1 == NULL || l2 == NULL) return false;@;
         %a@;
         l1 = l1 -> next;@;
         l2 = l2 -> next;@]@;}@]@;}"
        v1 v2 (generate_eq_type sub_v1 sub_v2) t

let generate_eq_elt v1 v2 fmt (name,typ) =
  let v1 fmt = Format.fprintf fmt "%t.%s" v1 name in
  let v2 fmt = Format.fprintf fmt "%t.%s" v2 name in
  generate_eq_type v1 v2 fmt typ

let generate_eq_field fmt arg =
  let v1 fmt = Format.pp_print_string fmt "(*v1)" in
  let v2 fmt = Format.pp_print_string fmt "(*v2)" in
  generate_eq_elt v1 v2 fmt arg

let generate_eq_constr_arg name const fmt arg =
  let v1 fmt = Format.fprintf fmt "v1->cons_%s.%s" name const in
  let v2 fmt = Format.fprintf fmt "v2->cons_%s.%s" name const in
  generate_eq_elt v1 v2 fmt arg

let generate_eq_case name fmt (const,l,_) =
  Format.fprintf fmt
    "@[<v 2>case %s: {@;%a@;return true;@]@;}"
    (String.uppercase_ascii const)
    (pretty_list (generate_eq_constr_arg name const)) l

let generate_equal fmt  { name; definition } =
  match definition with
    | Union l when has_only_const_constructors l ->
      Format.fprintf fmt
        "@[<v 2>bool %s_equal(const %s v1, const %s v2) {@;\
         return v1 == v2;@]@;}"
        name name name
    | Union l ->
      Format.fprintf fmt
        "@[<v 2>bool %s_equal(const %s v1, const %s v2) {@;\
         if (v1->tag_%s != v2->tag_%s) return false;@;\
         @[<v 2>switch (v1->tag_%s) {@;\
         %a\
         @]@;}@;\
         return false;\
         @]@;}"
        name name name name name name
        (pretty_list (generate_eq_case name)) l
    | Nuple(l,_) ->
      Format.fprintf fmt
        "@[<v 2>bool %s_equal(const %s v1, const %s v2) {@;\
         %a@;\
         return true;@]@;}"
        name name name (pretty_list generate_eq_field) l

let generate_c_dup fmt l =
  pretty_list ~pre:"@[<v 0>" ~sep:"@;@;" ~suf:"@;@;@]" generate_dup fmt l

let generate_c_destructor fmt l =
  pretty_list ~pre:"@[<v 0>" ~sep:"@;@;" ~suf:"@;@;@]" generate_destructor fmt l

let generate_c_equal fmt l =
  pretty_list ~pre:"@[<v 0>" ~sep:"@;@;" ~suf:"@;@;@]" generate_equal fmt l

let generate_output_proto fmt { name } =
  Format.fprintf fmt "void output_%s(FILE*,%s);" name name

let rec generate_output_typ name fmt = function
  | Bool ->
      Format.fprintf fmt
        "if (%t) fprintf(out,\"%%*strue\\n\",indent,\"\");@;\
         else fprintf(out,\"%%*sfalse\\n\",indent,\"\");" name
  | Int ->
      Format.fprintf fmt "fprintf(out,\"%%*s%%d\\n\",indent,\"\",%t);" name
  | Int64 ->
      Format.fprintf fmt "fprintf(out,\"%%*s%%\" PRId64 \"\\n\",indent,\"\",%t);" name
  | Location ->
      Format.fprintf fmt
        "@[<v 2>fprintf(out,\"%%*sloc\\n%%*s\\\"%%s\\\"\\n%%*s%%d\\n%%*s%%d\\n\
                  %%*s\\\"%%s\\\"\\n%%*s%%d\\n%%*s%%d\\n\",@;\
               indent,\"\",@;\
               indent+2,\"\",%t->filename1,@;\
               indent+2,\"\",%t->linenum1,@;\
               indent+2,\"\",%t->charnum1,@;\
               indent+2,\"\",%t->filename2,@;\
               indent+2,\"\",%t->linenum2,@;\
               indent+2,\"\",%t->charnum2@]@;);"
        name name name name name name
  | String ->
      Format.fprintf fmt 
        "fprintf(out,\"%%*s\\\"%%s\\\"\\n\",indent,\"\",%t);" name
  | Node s -> Format.fprintf fmt "output_%s(out,%t);" s name
  | Option typ ->
      let subname fmt = Format.fprintf fmt "%t->content" name in
      Format.fprintf fmt
        "@[<v 2>if (%t->is_some) {@;%a@]@;} else \
         fprintf(out,\"%%*snone\\n\",indent,\"\");"
        name (ptr_or_int subname) typ
  | List typ ->
      Format.fprintf fmt
        "@[<v 2>{ list elt = %t;@;\
         fprintf(out, elt?\"%%*sCons\\n\":\"%%*snil\\n\",indent,\"\");@;\
         indent+=2;@;\
         @[<v 2>while(elt) {@;%a@;elt=elt->next;@]@;}@;\
         indent-=2;@]@;}"
        name
        (ptr_or_int (fun fmt -> Format.pp_print_string fmt "elt->element")) typ

and ptr_or_int name fmt typ =
  Format.fprintf fmt
    "@[<v 0>%a content = (%a)%t.%s;@;%a@]"
    print_c_type typ
    print_c_type typ
    name
    (if is_base_type typ then "plain" else "container")
    (generate_output_typ (fun fmt -> Format.fprintf fmt "content"))
    typ

let generate_output_union_args union_name cons_name fmt (cons,typ) =
  generate_output_typ
    (fun fmt ->
      Format.fprintf fmt "obj -> cons_%s.%s.%s" union_name cons_name cons)
    fmt
    typ

let generate_output_field _name fmt (n,typ) =
  generate_output_typ
    (fun fmt -> Format.fprintf fmt "obj->%s" n) fmt typ

let generate_output_union name fmt (cons, args, _) =
  let handle_indent fmt action =
    match args with
      | [] -> ()
      | _ -> Format.fprintf fmt "indent%s=2;@;" action
  in
  Format.fprintf fmt
    "@[<v 2>case %s:@;fprintf(out,\"%%*s%%s\\n\",indent,\"\",\"%s\");@;\
     %a%a%afflush(out);@;break;@]@;"
    (String.uppercase_ascii cons) cons
    handle_indent "+"
    (pretty_list ~sep:"@;" ~suf:"@;" 
       (generate_output_union_args name cons))
    args
    handle_indent "-"

let generate_output_func fmt { name; definition } =
  match definition with
    | Union l ->
        let obj fmt name =
          if has_only_const_constructors l then
            Format.pp_print_string fmt "obj"
          else
            Format.fprintf fmt "obj -> tag_%s" name
        in
        Format.fprintf fmt 
          "@[<v 2>void output_%s(FILE* out,%s obj) {@;\
           @[<v 2>switch (%a) {@;%a@;\
           @[<v 2>default:@;\
               fprintf(out,\"%%*sunknown constructor %%d\\n\",\
                       indent,\"\",%a);@;fflush(out);@]\
           @;@]}@]@;}"
          name name
          obj name
          (pretty_list ~sep:"@;" (generate_output_union name)) l
          obj name
          
    | Nuple(l,_) ->
        Format.fprintf fmt
          "@[<v 2>void output_%s(FILE* out, %s obj) {@;\
           fprintf(out,\"%%*stuple\\n\",indent,\"\");@;\
           indent+=2;%aindent-=2;@;fflush(out);@]@;}"
           name name
          (pretty_list ~pre:"@;" ~sep:"@;" ~suf:"@;" 
             (generate_output_field name)) 
          l

let generate_c_output_proto fmt ast =
  pretty_list ~pre:"@[<v 0>" ~sep:"@;@;" ~suf:"@;@;@]"
    generate_output_proto fmt ast

let generate_c_output_func fmt ast =
  Format.fprintf fmt "@[<v 0>unsigned int indent = 0;@;%a@]"
    (pretty_list ~pre:"@;" ~sep:"@;@;" ~suf:"@;@;" generate_output_func) ast

let needed_headers = [ "inttypes"; "stdbool"; "stdint";
                       "stdlib"; "stdio"; "string"; "assert" ]

let include_std_header fmt s = Format.fprintf fmt "#include <%s.h>" s

let generate_c_file s ast =
  try
    let plain_file = Filename.chop_extension s in
    let code_name = plain_file ^ ".c" in
    let header_name = plain_file ^ ".h" in
    let code = open_out code_name in
    let header = open_out header_name in
    let cfmt = Format.formatter_of_out_channel code in
    let hfmt = Format.formatter_of_out_channel header in
    Format.fprintf cfmt
      "";
    Format.fprintf cfmt
      "@[<v 0>#include \"%s\"@;@;\
       @[<v 2>list cons_plain(long elt, list tl) {@;\
       list head = malloc(sizeof(struct _list));\
       if (head) { head->element.plain=elt; head->next=tl; }@;\
       return head;@]@;}@;\
       @[<v 2>list cons_container(void *elt, list tl) {@;\
       list head = malloc(sizeof(struct _list));@;\
       if (head) { head->element.container=elt; head->next=tl; }@;\
       return head;@]@;}@;\
       @[<v 2>option opt_none() {@;\
        option o = malloc(sizeof(struct _option));@;\
        if (o) { o->is_some = 0; o->content.plain=0; }@;\
        return o;\
       @]@;}@;\
       @[<v 2>option opt_some_plain(long elt) {@;\
        option o = malloc(sizeof(struct _option));@;\
        if (o) { o->is_some = 1; o->content.plain=elt; }@;\
        return o;\
       @]@;}@;\
       @[<v 2>option opt_some_container(void* elt) {@;\
        option o = malloc(sizeof(struct _option));@;\
        if (o) { o->is_some = 1; o->content.container=elt; }@;\
        return o;\
       @]@;}@;\
       @[<v 2>location cons_location(@[<hov 0>const char* f1,@ unsigned l1,@ \
       unsigned c1,@ const char* f2,@ unsigned l2, unsigned c2@]) {@;\
       location loc = malloc (sizeof(struct _location));@;\
       @[<v 2>if (loc) {\
       loc ->filename1 = f1;@;loc->linenum1 = l1;@;loc->charnum1 = c1;@;\
       loc ->filename2 = f2;@;loc->linenum2 = l2;@;loc->charnum2 = c2;@]@;}@;\
       return loc;@]@;}@;\
       @[<v 2>void memory_exhausted () {@;\
       fprintf(stderr, \"Fatal error: not enough memory\\n\");@;
       exit(2);@]@;}@;@;
       @[<v 2>location copy_loc(location source) {@;\
       location result = 0;@;\
       @[<v 2>if (source) {@;\
       result = (location) malloc(sizeof(struct _location));@;\
       if (!result) memory_exhausted();@;\
       result->filename1 = source->filename1?strdup(source->filename1):NULL;@;\
       result->filename2 = source->filename2?strdup(source->filename2):NULL;@;\
       result->linenum1 = source->linenum1;@;\
       result->linenum2 = source->linenum2;@;\
       result->charnum1 = source->charnum1;@;\
       result->charnum2 = source->charnum2;@]@;\
       }@;\
       return result;@]@;}@;\
       @[<v 2>void free_location(location source) {@;\
       if (source->filename1) free((char*) source->filename1);@;\
       if (source->filename2) free((char*) source->filename2);@;\
       free(source);@]@;\
       }@;@]"
      (Filename.basename header_name);
    Format.fprintf hfmt 
      "@[<v 0>#ifndef %s@;#define %s@;@;%a\
       @[<v 2>union ptr_or_int { long plain; void* container; };
       @[<v 2>typedef struct _list {@;\
        union ptr_or_int element;@;\
        struct _list* next;@]@;} *list;@;@;\
        list cons_plain(long,list);@;\
        list cons_container(void*, list);@;@;\
       @[<v 2>typedef struct _option {@;\
        int is_some;@; union ptr_or_int content;@]@;} *option;@;@;\
        option opt_none(void);@;\
        option opt_some_plain(long);@;\
        option opt_some_container(void*);@;@;\
       @[<v 2>typedef struct _location {@;\
           const char* filename1;@;\
           unsigned linenum1;@;\
           unsigned charnum1;@;\
           const char* filename2;@;\
           unsigned linenum2;@;\
           unsigned charnum2;@]@;} *location;@;\
       location cons_location(@[<hov 0>const char*,@;unsigned,@;unsigned,@;\
       const char*,@;unsigned,@;unsigned@]);@;\
       location copy_loc(location source);@;\
       void free_location(location source);@;\
      @;@]"
      (String.uppercase_ascii (Filename.basename plain_file))
      (String.uppercase_ascii (Filename.basename plain_file))
    (pretty_list ~sep:"@;" ~suf:"@;@;" include_std_header) needed_headers;
    generate_c_ast hfmt ast;
    generate_c_constructor cfmt ast;
    generate_c_destructor cfmt ast;
    generate_c_output_proto hfmt ast;
    generate_c_output_func cfmt ast;
    generate_c_dup cfmt ast;
    generate_c_equal cfmt ast;
    Format.fprintf hfmt "@[<v 0>#endif@]@.";
    Format.pp_print_flush cfmt ();
    close_out code;
    close_out header
  with Sys_error e ->
    Printf.eprintf "Unable to generate C bindings: %s\n%!" e

(* main functions *)

let parse_file s =
  let num_lines = ref 1 in
  let bol = ref 0 in
  let print_pos fmt ((l,b,c),e) =
    Printf.fprintf fmt "File %S, line %d, characters %d-%d:" s l (c - b) (e - b)
  in
  let print_top fmt toks =
    match Stream.peek toks with
      | None -> Printf.fprintf fmt "at end of file"
      | Some (Ident s | Kwd s) -> Printf.fprintf fmt "near token '%s'" s
      | Some (Genlex.String s) -> Printf.fprintf fmt "near token '%S'" s
      | Some (Genlex.Int i) -> Printf.fprintf fmt "near token '%d'" i
      | Some (Genlex.Float f) -> Printf.fprintf fmt "near token '%f'" f
      | Some (Genlex.Char c) -> Printf.fprintf fmt "near token ''%c''" c
  in
  let chan = 
    try open_in s
    with
        Sys_error e -> Printf.eprintf "Cannot open %s: %s\n%!" s e; exit 1
  in
  let chrs = Stream.of_channel chan in
  let next i =
    try
      match Stream.next chrs with
        | '\n' -> bol := i; incr num_lines; Some '\n'
        | c -> Some c
    with Stream.Failure -> None
  in
  let chrs = Stream.from next in
  let toks = lexer chrs in
  let lastloc = ref (1,0,0) in
  let next _ =
    lastloc:=(!num_lines, !bol, Stream.count chrs);
    try Some (Stream.next toks) with Stream.Failure -> None
  in
  let toks = Stream.from next in
  let error s =
    Printf.eprintf "%a\n%s %a\n%!"
      print_pos (!lastloc,Stream.count chrs) s print_top toks;
    exit 1
  in
  try
    parse_ast toks
  with
    | Stream.Failure -> error "Failure"
    | Stream.Error e -> error ("Error " ^ e)
    | Parsing.Parse_error -> error "Unexpected symbol"

let process s =
  let ast = parse_file s in
  fill_type_table ast;
  generate_ocaml_file s ast;
  generate_c_file s ast

let usage () =
  Printf.eprintf "Usage: gen_ast file.ast\n%!"

let () =
  if Array.length Sys.argv < 2 then usage ();
  process Sys.argv.(1)

(*
Local Variables:
compile-command: "make gen_ast"
End:
*)
