(** Homework 2

    ETPS: E (numbers and strings), T (primitive recursion), P (products),
    and S (sums).
*)

(**********************************************************************)
(** {1 Utilities} *)

let unimp s = failwith ("Unimplemented: " ^ s)

(**********************************************************************)

module F = Format
(** {1 Syntax}

    The pretty-printing functions

      {C [pp_]{i typ}[ : ]{i typ}[ -> string] }

    are defined here in terms of the {!Format} module in the standard
    library. Using the {!Format} module is optional. 
*)

open Base

type 'a fmt = F.formatter -> 'a -> unit

type 'a pp = 'a -> string

let pp_of_fmt fmt a =
  fmt F.str_formatter a;
  F.flush_str_formatter ()

type var = string [@@deriving sexp_of, compare, equal]

let f_var : var fmt = F.pp_print_string

let pp_var : var pp = fun x -> x

type num = int [@@deriving sexp_of, compare, equal]

let f_num : num fmt = F.pp_print_int

let pp_num : num pp = Int.to_string

type str = string [@@deriving sexp_of, compare, equal]

let f_str : str fmt = F.pp_print_string

let pp_str : str pp = fun s -> s

type typ =
  | TNum
  | TStr
  | Nat
  | Arr of typ * typ
  | Unit
  | Prod of typ * typ
  | Void
  | Sum of typ * typ
[@@deriving sexp_of, compare, equal]

let rec f_typ f = function
  | TNum -> F.fprintf f "num"
  | Arr (t1, t2) -> F.printf "%a -> %a" f_typ t1 f_typ t2
  | _ -> unimp "f_typ"

let pp_typ : typ -> string = pp_of_fmt f_typ

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
[@@deriving sexp_of, compare, equal]

let pp_exp_sexp e = pp_of_fmt Ppx_sexp_conv_lib.Sexp.pp_hum (sexp_of_exp e)

let rec f_exp f = function
  | Var x -> f_var f x
  | Num n -> f_num f n
  | Plus (e1, e2) -> F.fprintf f "(@[%a@ +@ %a@])" f_exp e1 f_exp e2
  | _ -> unimp "f_exp"

let pp_exp : exp pp = pp_of_fmt f_exp

(**********************************************************************)
(** {1 Values} *)

let is_val : exp -> bool = function
  | Num _ -> true
  | _ -> unimp "is_val"

(**********************************************************************)
(** {1 Typing} *)

type typctx = unit (* TODO: replace *)

let pp_typctx : typctx pp = fun _ -> "todo"

let emp : typctx = () (* TODO: replace *)

let lookup (gamma : typctx) (x : var) : typ option = unimp "lookup"

let extend (gamma : typctx) (x : var) (tau : typ) : typctx = unimp "extend"

let rec exp_typ (gamma : typctx) : exp -> typ option =
  (* Open the Base.Option library for some convenience functions on
     options. Comment out the following line to remove the library
     dependency on Base. *)
  let open Base.Option in
  (* Let_syntax enables the syntax shown below in the "Times" case,
     which is similar to Haskell do notation.  Plus and Times cases
     here are functionally identical, so just choose whichever monad
     syntax you're more comfortable with.
   *)
  let open Base.Option.Let_syntax in
  function
  | Num _ -> Some TNum
  | Plus (e1, e2) ->
      exp_typ gamma e1 >>= fun tau1 ->
      exp_typ gamma e2 >>= fun tau2 ->
      some_if (equal_typ tau1 TNum && equal_typ tau2 TNum) TNum
  | Times (e1, e2) ->
      let%bind tau1 = exp_typ gamma e1 in
      let%bind tau2 = exp_typ gamma e2 in
      some_if (equal_typ tau1 TNum && equal_typ tau2 TNum) TNum
  | _ -> unimp "exp_typ"

(**********************************************************************)
(** {1 Substitution} *)

let subst (e' : exp) (x : var) : exp -> exp = function
  (* Be very careful with Var expressions. *)
  | Var y when equal_var x y -> unimp "subst"
  | Var y -> unimp "subst"
  | _ -> unimp "subst"

(**********************************************************************)
(** {1 Evaluation} *)

let rec eval e =
  match e with
  | Num _ -> e
  | Plus (e1, e2) -> (
      match (eval e1, eval e2) with
      | Num n1, Num n2 -> Num (n1 + n2)
      | _ -> invalid_arg (pp_exp e) )
  | _ -> unimp "eval"

(**********************************************************************)
(** {1 Reduction} *)

let step (e : exp) : exp = unimp "step"

let steps_pap (tau : typ) (e : exp) : exp = unimp "step_pap"

(**********************************************************************)
(** {1 Tests} *)
                                          
module Test = struct
  (********************************************************************)
  (** {2 Utilities} *)

  let pp_option (pp : 'a -> string) : 'a option -> string = function
    | None -> "None"
    | Some a -> F.sprintf "Some @[%a@]" (fun () -> pp) a

  (********************************************************************)
  (** {2 Expressions} *)

  let num_1 = Num 1

  let num_2 = Num 2

  let plus_1_1 = Plus (num_1, num_1)

  (********************************************************************)
  (** {2 Example Tests} *)
  (* Write tests as below: `let%test "test name" = <boolean>`*)
  (* Run tests with `dune runtest` *)

  let%test "one is a val" = is_val num_1

  let%test "plus is not a val" = not @@ is_val plus_1_1

  let has_type gamma exp tau =
    match exp_typ gamma exp with
    | None -> false
    | Some tau' -> equal_typ tau tau'

  let%test "num_1 : TNum" = has_type emp num_1 TNum

  let%test "plus_1_1 : TNum" = has_type emp plus_1_1 TNum

  let%test "num_1 --> num_1" = equal_exp num_1 (step num_1)

  let%test "plus_1_1 -> num_2" = equal_exp num_2 (step plus_1_1)
end
