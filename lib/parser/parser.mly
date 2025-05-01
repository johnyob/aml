%{
open Grace
open Aml_ast 
open Ast_types
open Ast_builder.Default

let range_of_lex lex = 
  Range.of_lex ?source:(Aml_source.get ()) lex
;; 
%}

%start  parse_core_type parse_expression parse_structure
%type <Ast.structure> parse_structure
%type <Ast.expression> parse_expression
%type <Ast.core_type> parse_core_type

%%

(** {1 Start Symbols} *)

parse_structure:
  str = structure; EOF 
    { str }

parse_expression:
  exp = expression; EOF 
    { exp }

parse_core_type:
  type_ = core_type; EOF 
    { type_ }

(** {2 Standard Library Extensions} 

    This section contains definitions of several generic parameterized rules that 
    are useful for parsing aml. *)

(** [seperated_nontrivial_list(sep, X)] parases a list containing at least two [X]s 
    separated by [sep]. *)
separated_nontrivial_list(sep, X):
    x1 = X
    ; sep
    ; x2 = X
      { [ x1; x2 ] }
  | x = X
    ; sep
    ; xs = separated_nontrivial_list(sep, X)
      { x :: xs }

(** [preceded_or_separated_nonempty_list(sep, X)] parses a non-emppty list of [X]s separated 
    by [sep], optionally preceded by [sep]. *)
%inline preceded_or_separated_nonempty_list(sep, X):
  ioption(sep); xs = separated_nonempty_list(sep, X)
    { xs }


(** {3 Core Types} 

    This section contains the rules for parsing the grammar of core types:
    {v
      tau ::=   
        | 'a                (* variables *) 
        | tau -> tau        (* functions *)
        | tau = tau         (* equality types *)
        | overline(tau) T   (* type constructors *)
        | bot               (* empty type *)
    v} 
    
    The grammar is {e stratified} to handle the precedence issues that arise. *)

type_var_name:
  "'"; id = "<ident>"
    { type_var_name ~range:(range_of_lex $loc) id }

type_name:
  id = "<ident>"
    { type_name ~range:(range_of_lex $loc) id }

%inline core_type:
  type_ = arrow_type
    { type_ }

arrow_type:
    type_ = eq_type 
      { type_ }   
  | type1 = eq_type 
    ; "->"
    ; type2 = arrow_type 
      { Type.arrow ~range:(range_of_lex $loc) type1 type2 }

eq_type:
    type_ = atom_type
      { type_ }
  | type1 = atom_type 
    ; "="
    ; type2 = atom_type 
      { Type.eq ~range:(range_of_lex $loc) type1 type2 }

atom_type:
    "("
    ; type_ = core_type
    ; ")"
      { type_ }
  | "bot"
      { Type.bot ~range:(range_of_lex $loc) }
  | type_var_name = type_var_name
      { Type.var ~range:(range_of_lex $loc) type_var_name }
  | arg_types = type_argument_list
    ; type_name = type_name
      { Type.constr ~range:(range_of_lex $loc) arg_types type_name }

%inline type_argument_list:
    (* empty *)   
      { [] }
  | type_ = atom_type 
      { [ type_ ] }
  | "("
    ; types = separated_nontrivial_list(",", core_type)
    ; ")"
      { types }


(** {4 Expressions and Patterns} 

    This section contains the rules for parsing the grammar of expressions
    {v
      e ::= 
        | x                                 (* variable *)
        | const                             (* constants *)
        | fun overline(x) -> e              (* functions *)
        | e e                               (* function application *)
        | forall (type overline('a)) -> e   (* type exists binder *)
        | (e : tau)                         (* type annotation *)
        | Refl                              (* refl *)
        | match e : tau with Refl -> e      (* match *)
        | let vb in e                       (* let *)

      vb ::= x = e                          (* value binding *)
    v} 
*)

%inline var_name:
  id = "<ident>"
    { var_name ~range:(range_of_lex $loc) id }

constant:
    int = "<int>"
      { Const_int int }
  | "true"
      { Const_bool true }
  | "false"
      { Const_bool false }
  | "()"
      { Const_unit }

expression:
    exp = app_expression 
      { exp }
  | "fun"
    ; vars = nonempty_list(var_name)
    ; "->"
    ; exp = expression 
      { Expression.fun_ ~range:(range_of_lex $loc) vars exp }
  | "forall"
    ; "("
    ; "type"
    ; type_var_names = nonempty_list(type_var_name)
    ; ")"
    ; "->"
    ; exp = expression
      { Expression.forall ~range:(range_of_lex $loc) type_var_names exp }
  | "match" 
    ; exp = expression 
    ; ":"
    ; annot = core_type
    ; "with"
    ; "Refl"
    ; "->"
    ; case = expression
      { Expression.match_ ~range:(range_of_lex $loc) exp ~annot ~with_:case }
  | "let"
    ; value_binding = value_binding
    ; "in"
    ; exp = expression
      { Expression.let_ ~range:(range_of_lex $loc) value_binding ~in_:exp }

app_expression:
    exp = atom_expression
      { exp }
  | exp1 = app_expression
    ; exp2 = atom_expression
      { Expression.app ~range:(range_of_lex $loc) exp1 exp2 }

value_binding:
  var_name = var_name 
  ; "="
  ; exp = expression
    { value_binding ~range:(range_of_lex $loc) var_name exp }

atom_expression:
    const = constant 
      { Expression.const ~range:(range_of_lex $loc) const }
  | var_name = var_name
      { Expression.var ~range:(range_of_lex $loc) var_name }
  | "Refl"
      { Expression.refl ~range:(range_of_lex $loc) }
  | "absurd"
      { Expression.absurd ~range:(range_of_lex $loc) }
  | "("
    ; exp = expression
    ; ":"
    ; type_ = core_type
    ; ")"
      { Expression.annot ~range:(range_of_lex $loc) exp type_ }
  | "("
    ; exp = expression
    ; ")"
      { exp }

(** {5 Structures} 

    Structures are simply a list of type definitons, primitive declarations and 
    value bindings. 
*)

core_scheme:
    type_var_names = nonempty_list(type_var_name)
    ; "."
    ; type_ = core_type
      { Type.scheme ~range:(range_of_lex $loc) ~quantifiers:type_var_names type_ }
  | type_ = core_type
      { Type.scheme ~range:(range_of_lex $loc) type_ }

type_declaration: 
  "type"
  ; params = type_param_list 
  ; name = type_name 
  ; kind = type_decl_kind 
      { Structure.type_decl ~range:(range_of_lex $loc) ~name ~params kind }

type_decl_kind:
    (* empty *)
      { Type_decl_abstract }

%inline type_param_list:
    (* empty *)   
      { [] }
  | type_var_name = type_var_name 
      { [ type_var_name ] }
  | "("
    ; type_var_names = separated_nontrivial_list(",", type_var_name)
    ; ")"
      { type_var_names }

value_description:
    name = var_name 
  ; ":"
  ; scheme = core_scheme 
      { Structure.value_desc ~range:(range_of_lex $loc) ~name ~type_:scheme }

structure_item:
    "let"
    ; value_binding = value_binding
      { Structure.value ~range:(range_of_lex $loc) value_binding }
  | "external"
    ; value_desc = value_description
      { Structure.primitive ~range:(range_of_lex $loc) value_desc }
  | type_decl = type_declaration
      { Structure.type_ ~range:(range_of_lex $loc) type_decl }
  
terminated_structure_item:
  str_item = structure_item
  ; ";;"
    { str_item }

structure:
  structure = nonempty_list(terminated_structure_item)
    { structure }

