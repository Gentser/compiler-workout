(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

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

    (* Expression evaluator

          val eval : state -> t -> int

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

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval config statement =
      let (state, input, output) = config in
      match statement with
        (* <s, i, o> --> <s[ x<-[|e|]s ], i, o> *)
        | Assign (var_name, expression) -> (Expr.update var_name (Expr.eval state expression) state, input, output)
        (* <s, z::i, o> --> <s[x<-z], i, o> *)
        | Read var_name -> (match input with  (* check for existing of tail - no error check*)
          | head::tail -> (Expr.update var_name head state, tail, output))
        (* <s, i, o> --> <s, i, o @ [ [|e|]s ]> *)
        | Write expression -> (state, input, output @ [Expr.eval state expression])
        (* C1 -S1-> C' -S2-> C2*)
        | Seq (state1, state2) -> eval (eval config state1) state2;;

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
