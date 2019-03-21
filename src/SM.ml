open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)

(* Hard expression for left-folding - desicion to make rec function *)
let rec eval env ((stack, ((state, input, output) as c)) as config) = function
| [] -> config
| instruction :: rest_instr ->
     match instruction with
     | BINOP op ->
        begin
          match stack with
          | y::x::rest -> (* y::x - because order of arguments on the stack is inverted *)
             eval env ((Language.Expr.evalOperation op x y) :: rest, c) rest_instr
          | _ -> failwith "SM interpreter error: BINOP"
        end
     | CONST v -> eval env (v::stack, c) rest_instr
     | READ ->
        begin
          match input with
          | x::rest -> eval env (x::stack, (state, rest, output)) rest_instr
          | _ -> failwith "SM interpreter error: READ"
        end
     | WRITE ->
        begin
          match stack with
          | x::rest -> eval env (rest, (state, input, output @ [x])) rest_instr
          | _ -> failwith "SM interpreter error: WRITE"
        end
     | LD x -> eval env ((state x) :: stack, c) rest_instr
     | ST x ->
        begin
          match stack with
          | z::rest -> eval env (rest, ((Language.Expr.update x z state), input, output)) rest_instr
          | _ -> failwith "SM interpreter error: ST"
        end
     | LABEL l -> eval env config rest_instr
     | JMP l -> eval env config (env#labeled l)
     | CJMP (b, l) ->
        begin
          match stack with
          | x::rest ->
              if (x = 0 && b = "z" || x != 0 && b = "nz")
              then eval env (rest, c) (env#labeled l)
              else eval env (rest, c) rest_instr
          | _ -> failwith "SM interpreter error: stack is empty"
        end

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile =

  let rec expr = function
  | Language.Expr.Var   x          -> [LD x]
  | Language.Expr.Const n          -> [CONST n]
  | Language.Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  in

  let label_generator =
    object
      val mutable counter = 0
      method generate =
        counter <- counter + 1;
        "l_" ^ string_of_int counter
    end
  in

  function
  | Language.Stmt.Seq (s1, s2)   -> compile s1 @ compile s2
  | Language.Stmt.Read x         -> [READ; ST x]
  | Language.Stmt.Write e        -> expr e @ [WRITE]
  | Language.Stmt.Assign (x, e)  -> expr e @ [ST x]

  | Language.Stmt.Skip           -> []
  | Language.Stmt.If (e, s1, s2) ->
     let l_else = label_generator#generate in
     let l_fi = label_generator#generate in
     (expr e) @ [CJMP ("z", l_else)] @ (compile s1) @ [JMP l_fi] @ [LABEL l_else] @ (compile s2) @ [LABEL l_fi]

  | Language.Stmt.While (e, s) ->
     let l_expr = label_generator#generate in
     let l_od = label_generator#generate in
     [LABEL l_expr] @ (expr e) @ [CJMP ("z", l_od)] @ (compile s) @ [JMP l_expr] @ [LABEL l_od]

  | Language.Stmt.RepeatUntil (e, s) ->
     let l_repeat = label_generator#generate in
     [LABEL l_repeat] @ (compile s) @ (expr e) @ [CJMP ("z", l_repeat)]
