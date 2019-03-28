(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators

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


    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string

    *)
    (* Auxiliary function for binary operation performance - instead of function repeat bellow *)
    let parseBinOp op = ostap( $(op) ), (fun x y -> Binop (op, x, y))
    ostap (
        parse: expr;
        expr:
      	    !(Ostap.Util.expr
      		    (fun x -> x)  (* identity function *)
      		    (Array.map (fun (asc, ops) -> asc, List.map parseBinOp ops)
                    [|
                        `Lefta, ["!!"];
                        `Lefta, ["&&"];
                        `Nona , ["=="; "!="];
                        `Nona , ["<="; "<"; ">="; ">"];
                        `Lefta, ["+"; "-"];
                        `Lefta, ["*"; "/"; "%"];
                    |]
                )
      		    primary
      		);
      	primary: c:DECIMAL {Const c} | x:IDENT {Var x} | -"(" expr -")"  (* simpiest expression - {var, const, (var), (const)}*)
    )

  end

(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | RepeatUntil of t * Expr.t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list

    (* Statement evaluator

         val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)

    let reverseCondition c = Expr.Binop ("==", c, Expr.Const 0)
    let headToTail t m = match t with
        | head::tail -> (head, tail)
        | _ -> failwith(m)

    let rec eval (s, i, o) p = match p with
        (* <s, i, o> --> <s[ x<-[|e|]s ], i, o> *)
        | Assign (name, e)          -> (Expr.update name (Expr.eval s e) s, i, o)
        (* <s, z::i, o> --> <s[x<-z], i, o> *)
        | Read name                 -> let (head, tail) = headToTail i "Unexpected end of input (no info)" in
                                       (Expr.update name head s, tail, o)
        (* <s, i, o> --> <s, i, o @ [ [|e|]s ]> *)
        | Write e                   -> (s, i, o @ [Expr.eval s e])
        (* C1 -S1-> C' -S2-> C2*)
        | Seq (e1, e2)              -> let (s1, i1, o1) = eval (s, i, o) e1 in
                                       eval (s1, i1, o1) e2

        | Skip                      -> (s, i, o)
        | If (cond, thn, els)       -> let cv = Expr.eval s cond in
                                       if cv <> 0 then
                                           eval (s, i, o) thn
                                       else
                                           eval (s, i, o) els

        | While (cond, body)        -> let cv = Expr.eval s cond in
                                       if cv == 0 then (s, i, o)
                                       else
                                           let c' = eval (s, i, o) body in
                                           eval c' (While (cond, body))

        | RepeatUntil (body, cond)  -> let c' = eval (s, i, o) body in
                                       eval c' (While (reverseCondition cond, body));;

    (* Statement parser - more complex structure than previous*)
    ostap (
      parse: st1:stmt ";" st2:parse {Seq (st1, st2)} | stmt;
      stmt: "read" "(" x:IDENT ")" {Read x}                 (* Read *)
           | "write" "(" e:!(Expr.parse) ")" {Write e}      (* Write *)
           | x:IDENT ":=" e:!(Expr.parse) {Assign (x, e)}   (* Assign *)

           (* Cycles ends with the inverted start-word (ex: if ... fi) *)
           | "if" condition:!(Expr.parse)
                "then" th:!(parse)
                elif:(%"elif" !(Expr.parse) %"then" !(parse))*
                els:(%"else" !(parse))?
                "fi"
                {
                    let else_body = match els with
                        | Some x -> x
                        | _ -> Skip
                    in
                    let t = List.fold_right (fun (cond, body) curr -> If (cond, body, curr)) elif else_body in
                    If (condition, th, t)
                }
            | "while" condition:!(Expr.parse) "do" body:!(parse) "od" { While (condition, body)}
            | "for" init:!(parse) "," cond:!(Expr.parse) "," step:!(parse) "do" body:!(parse) "od"
            {
                Seq(init, While(cond, Seq(body, step)))
            }
            | "repeat" body:!(parse) "until" cond:!(Expr.parse)
            {
                RepeatUntil (body, cond)
            }
            | "skip" {Skip}
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o

(* Top-level parser *)
let parse = Stmt.parse
