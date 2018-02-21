(** Homework 2

    ETPS: E (numbers and strings), T (primitive recursion), P (products),
    and S (sums).
*)

(**********************************************************************)
(** {1 Utilities} *)

let unimp: string -> 'a = fun s -> failwith ("Unimplemented: " ^ s)

(**********************************************************************)
(** {1 Syntax}

    The pretty-printing functions

      {C [pp_]{i typ}[ : ]{i typ}[ -> string] }

    are defined here in terms of the {!Format} module in the standard
    library. Using the {!Format} module is optional. 
*)

module F = Format
let pp_of_fmt (f: F.formatter -> 'a -> unit): 'a -> string = fun a ->
  f F.str_formatter a; F.flush_str_formatter ()

type var = string
let f_var = F.pp_print_string
let pp_var: var -> string = fun x -> x

type num = int
let f_num = F.pp_print_int
let pp_num = string_of_int

type str = string
let f_str = F.pp_print_string
let pp_str: str -> string = fun s -> s

type typ =
  | TNum
  | TStr
  | Nat
  | Arr of typ * typ
  | Unit
  | Prod of typ * typ
  | Void
  | Sum of typ * typ
let f_typ f = function
  | TNum -> F.fprintf f "num"
  | _ -> unimp "f_typ"
let pp_typ: typ -> string = pp_of_fmt f_typ

type exp =
  | Var of var
  | Num of num
  | Str of str
  | Plus of exp * exp
  | Times of exp * exp
  | Cat of exp * exp
  | Len of exp
  | Let of exp * var * exp
  | Z
  | S of exp
  | Rec of exp * var * var * exp * exp
  | Lam of var * typ * exp
  | Ap of exp * exp
  | Triv
  | Pair of exp * exp
  | PrL of exp
  | PrR of exp
  | Abort of typ * exp
  | InL of typ * typ * exp
  | InR of typ * typ * exp
  | Case of exp * var * exp * var * exp
let rec f_exp f =
  function
  | Var x -> F.fprintf f "%a" f_var x
  | Num n -> F.fprintf f "%a" f_num n
  | Plus (e1,e2) -> F.fprintf f "(@[%a@ +@ %a@])" f_exp e1 f_exp e2
  | _ -> unimp "f_exp"
let pp_exp: exp -> string = pp_of_fmt f_exp

(**********************************************************************)
(** {1 Values} *)

let is_val: exp -> bool = function
  | Num _ -> true
  | _ -> unimp "is_val"

(**********************************************************************)
(** {1 Typing} *)

type typctx = unit (* TODO: replace *)
let pp_typctx: typctx -> string = fun _ -> "todo"

let emp: typctx = () (* TODO: replace *)
let lookup: typctx -> var -> typ option = fun gamma x -> unimp "lookup"
let extend: typctx -> var -> typ -> typctx = fun gamma x tau -> unimp "extend"

let rec exp_typ: typctx -> exp -> typ option = fun gamma ->
  (* Open the Base.Option library for some convenience functions on
     options. Comment out the following line to remove the library
     dependency on Base. *)
  let open Base.Option in 
  function
  | Num _ -> Some TNum
  | Plus (e1, e2) ->
     exp_typ gamma e1 >>= fun tau1 ->
     exp_typ gamma e2 >>= fun tau2 ->
     some_if (tau1 == TNum && tau2 == TNum) TNum
  | _ -> unimp "exp_typ"

(**********************************************************************)
(** {1 Substitution} *)

let subst: exp -> var -> exp -> exp = fun e' x ->
  function
  (* Be very careful with Var expressions. *)
  | Var y when x = y -> unimp "subst"
  | Var y -> unimp "subst"
  | _ -> unimp "subst"

(**********************************************************************)
(** {1 Evaluation} *)

let rec eval: exp -> exp = fun e ->
  match e with
  | Num _ -> e
  | Plus (e1, e2) ->
     begin match eval e1, eval e2 with
     | Num n1, Num n2 -> Num (n1 + n2)
     | _ -> invalid_arg (pp_exp e)
     end
  | _ -> unimp "eval"
       
(**********************************************************************)
(** {1 Reduction} *)

let step: exp -> exp = fun e -> unimp "step"
let steps_pap: typ -> exp -> exp = fun tau e -> unimp "step_pap"

