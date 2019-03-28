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
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let hd_tl = Language.Stmt.headToTail
let cjmp_sat znz value = if (znz = "nz" && value <> 0) || (znz = "z" && value == 0) then true else false

let rec eval env (stack, (state, input, output)) p = if 1 == 0 then (stack, (state, input, output)) else
    let eval_expr expr = match expr with
        | BINOP op -> (match stack with
            | (y::x::xs) -> (Language.Expr.to_func op x y :: xs, (state, input, output))
            | _ -> failwith "SM interpreter error: BINOP")
        | CONST x -> (x :: stack, (state, input, output))
        | READ -> let (head, tail) = hd_tl input "SM interpreter error: READ" in
                      (head :: stack, (state, tail, output))
        | WRITE -> let (head, tail) = hd_tl stack "SM interpreter error: WRITE" in
                       (tail, (state, input, output @ [head]))
        | LD name -> (state name :: stack, (state, input, output))
        | ST name -> let (head, tail) = hd_tl stack "SM interpreter error: ST" in
                     let new_state = Language.Expr.update name head state in
                     (tail, (new_state, input, output))
        | LABEL _ -> (stack, (state, input, output))
        | _ -> failwith "SM interpreter error: Unexpected statement"
    in match p with
        | x::xs -> (match x with
            | JMP label -> eval env (stack, (state, input, output)) (env#labeled label)
            | CJMP (znz, label) -> let (head, tail) = hd_tl stack "SM interpreter error: CJMP" in
                if cjmp_sat znz head
                then eval env (tail, (state, input, output)) (env#labeled label)
                else eval env (tail, (state, input, output)) xs
            | _ -> eval env (eval_expr x) xs)
        | _ -> (stack, (state, input, output))

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
  if (1 == 0) then
  List.fold_left (fun () pr ->
                  Printf.printf "%s\n" (GT.transform(insn) (new @insn[show]) () pr)) () p
  else ();
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
(* Label generator *)
class labels =
  object (self)
    val label_n = 0
    method get_label = {< label_n = label_n + 1 >}, self#generate_label
    method generate_label = "label" ^ string_of_int label_n
end

(* Primitive compilation *)
let rec compile_expr expr = match expr with
  | Language.Expr.Var   x               -> [LD x]
  | Language.Expr.Const n               -> [CONST n]
  | Language.Expr.Binop (op, x, y)      -> compile_expr x @ compile_expr y @ [BINOP op]

(* Statement compilation *)
let rec compile_impl lb p after_label = match p with
    | Language.Stmt.Seq (e1, e2)        -> let (lb, label) = lb#get_label in
                                           let (prg1, used1, lb) = compile_impl lb e1 label in
                                           let (prg2, used2, lb) = compile_impl lb e2 after_label in
                                           (prg1 @ (if used1 then [LABEL label] else []) @ prg2), used2, lb
    | Language.Stmt.Read name           -> ([READ; ST name]), false, lb
    | Language.Stmt.Write expr          -> (compile_expr expr @ [WRITE]), false, lb
    | Language.Stmt.Assign (name, expr) -> (compile_expr expr @ [ST name]), false, lb

    | Language.Stmt.Skip                -> [], false, lb
    | Language.Stmt.If (cond, thn, els) ->
        let lb, else_label = lb#get_label in
        let condition = compile_expr cond in
        let (thn_body, used1, lb) = compile_impl lb thn after_label in
        let (els_body, used2, lb) = compile_impl lb els after_label in
        condition @ [CJMP ("z", else_label)] @
        thn_body @ (if used1 then [] else [JMP after_label]) @ [LABEL else_label] @
        els_body @ (if used2 then [] else [JMP after_label])
        , true, lb

    | Language.Stmt.While (cond, body)  ->
        let lb, before_label = lb#get_label in
        let lb, condition_label = lb#get_label in
        let do_body, _, lb = compile_impl lb body condition_label in
        let condition = compile_expr cond in
        [JMP condition_label; LABEL before_label] @
        do_body @ [LABEL condition_label] @ condition @ [CJMP ("nz", before_label)]
        , false, lb

    | Language.Stmt.RepeatUntil (body, cond) ->
        let (prg, _, lb) = compile_impl lb (Language.Stmt.While (
                                            Language.Stmt.reverseCondition cond, body)) after_label in
        List.tl (prg), false, lb

(* SM compiler itself *)
let rec compile p = let lb, label = (new labels)#get_label in
                    let prg, used, _ = compile_impl lb p label in
                    prg @ (if used then [LABEL label] else [])
