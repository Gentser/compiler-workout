open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)
 let process_instruct config instruct =
    let (stack, c) = config in
    let (state, input, output) = c in
      match instruct with
        | BINOP op -> (match stack with
                        (* y::x - because order of arguments on the stack is inverted *)
                        | y::x::rest -> [Syntax.Expr.evalOperation op x y] @ rest, c
                      )
        | CONST x  -> [x] @ stack, c
        | READ     -> (match input with
                        | x::rest -> [x] @ stack, (state, rest, output)
                      )
        | WRITE    -> (match stack with
                        | x::rest -> rest, (state, input, output @ [x])
                      )
        | LD var   -> [state var] @ stack, c
        | ST var   -> (match stack with
                        | x::rest -> rest, (Syntax.Expr.update var x state, input, output)
                      )

   let eval config prog = List.fold_left process_instruct config prog;;

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)

 (* Expression needs in their own compiler *)
  let rec compileE e = match e with
      | Syntax.Expr.Const n -> [CONST n]
      | Syntax.Expr.Var x -> [LD x]
      | Syntax.Expr.Binop (operator, left, right) -> (compileE left) @ (compileE right) @ [BINOP operator];;

  let rec compile program = match program with
      | Syntax.Stmt.Assign (x, e) -> (compileE e) @ [ST x]
      | Syntax.Stmt.Read x -> [READ; ST x]
      | Syntax.Stmt.Write e -> (compileE e) @ [WRITE]
      | Syntax.Stmt.Seq (a, b) -> (compile a) @ (compile b);;
