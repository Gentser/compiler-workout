(* Simple expressions: syntax and semantics *)

(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* The type for the expression. Note, in regular OCaml there is no "@type..."
   notation, it came from GT.
*)
@type expr =
  (* integer constant *) | Const of int
  (* variable         *) | Var   of string
  (* binary operator  *) | Binop of string * expr * expr with show

(* Available binary operators:
    !!                   --- disjunction
    &&                   --- conjunction
    ==, !=, <=, <, >=, > --- comparisons
    +, -                 --- addition, subtraction
    *, /, %              --- multiplication, division, reminder
*)

(* State: a partial map from variables to integer values. *)
type state = string -> int

(* Empty state: maps every variable into nothing. *)
let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

(* Update: non-destructively "modifies" the state s by binding the variable x
   to value v and returns the new state.
*)
let update x v s = fun y -> if x = y then v else s y

(* An example of a non-trivial state: *)
let s = update "x" 1 @@ update "y" 2 @@ update "z" 3 @@ update "t" 4 empty

(* Some testing; comment this definition out when submitting the solution. *)
(* let _ =
  List.iter
    (fun x ->
       try  Printf.printf "%s=%d\n" x @@ s x
       with Failure s -> Printf.printf "%s\n" s
    ) ["x"; "a"; "y"; "z"; "t"; "b"] *)

(* Expression evaluator

     val eval : state -> expr -> int

   Takes a state and an expression, and returns the value of the expression in
   the given state.
*)
let boolToInt b = if b then 1 else 0

let intToBool i = i != 0

let fun1 op = fun x1 x2 -> boolToInt(op x1 x2)
let fun2 op = fun x1 x2 -> boolToInt (op (intToBool x1) (intToBool x2))

let evalOperation op =
   match op with

   (* These opearators were defined in Embedding.ml *)
   | "+"  -> ( + )
   | "-"  -> ( - )
   | "*"  -> ( * )
   | "/"  -> ( / )
   | "%"  -> ( mod )

   (* According to 01.pdf result of following operations is converted to int *)
   | "==" -> fun1 ( == )
   | "!=" -> fun1 ( != )
   | "<=" -> fun1 ( <= )
   | "<"  -> fun1 ( <  )
   | ">=" -> fun1 ( >= )
   | ">"  -> fun1 ( >  )

   (* According to 01.pdf arguments of following operations are converted to bool *)
   | "&&" -> fun2 ( && )
   | "!!" -> fun2 ( || )

   (* Unknown operator *)
   | _    -> failwith (Printf.sprintf "Unknown operator");;

let rec eval state exp =
   match exp with
   | Const v -> v
   | Var x -> state x
   | Binop (op, x1, x2) -> evalOperation op (eval state x1) (eval state x2)
