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
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let hd_tl = Language.Stmt.headToTail
let cjmp_sat znz value = if (znz = "nz" && value <> 0) || (znz = "z" && value == 0) then true else false

let rec eval env (callstack, stack, ((state, input, output) as config)) p =
    if 1 == 0 then (callstack, stack, config) else
    let eval_expr expr = match expr with
        | BINOP op -> (match stack with
            | (y::x::xs) -> (Language.Expr.to_func op x y :: xs, config)
            | _ -> failwith "SM interpreter error: BINOP")
        | CONST x -> (x :: stack, config)
        | READ -> let (head, tail) = hd_tl input "SM interpreter error: READ" in
                      (head :: stack, (state, tail, output))
        | WRITE -> let (head, tail) = hd_tl stack "SM interpreter error: WRITE" in
                       (tail, (state, input, output @ [head]))
        | LD name -> ((Language.State.eval state name) :: stack, config)
        | ST name -> let (head, tail) = hd_tl stack "SM interpreter error: ST" in
                     let new_state = Language.State.update name head state in
                     (tail, (new_state, input, output))
        | LABEL _ -> (stack, config)
        | BEGIN (_, arg_names, locals) ->
                let fun_state = Language.State.enter state (arg_names @ locals) in
                let new_state, stack_left =
                    List.fold_left (fun (state, x::stack) name -> (State.update name x state, stack))
                         (fun_state, stack) arg_names in
                (stack_left, (new_state, input, output))
        | _ -> failwith "SM interpreter error: Unexpected statement"

    in match p with
        | x::xs -> (match x with
            | JMP label -> eval env (callstack, stack, config) (env#labeled label)
            | CJMP (znz, label) -> let (head, tail) = hd_tl stack "SM interpreter error: CJMP" in
                if cjmp_sat znz head
                then eval env (callstack, tail, config) (env#labeled label)
                else eval env (callstack, tail, config) xs
            | CALL (f, _, _) -> eval env ((xs, state)::callstack, stack, config) (env#labeled f)
            |RET _ | END -> (match callstack with
                | (p, old_s)::callstack' ->
                    let new_state = Language.State.leave state old_s in
                    eval env (callstack', stack, (new_state, input, output)) p
                | _ -> (callstack, stack, config)
                )
            | _ -> let (stack, config) = eval_expr x in
                   eval env (callstack, stack, config) xs)
        | _ -> (callstack, stack, config)

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
  | Language.Expr.Call (f, args)        -> let compile_args = List.concat (List.map (compile_expr) (List.rev args)) in
                                           compile_args @ [CALL (f, List.length args, true)]

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

    | Language.Stmt.Repeat (body, cond) ->
        let (prg, _, lb) = compile_impl lb (Language.Stmt.While (
                                            Language.Stmt.reverseCondition cond, body)) after_label in
        List.tl (prg), false, lb

    | Language.Stmt.Call (f, args) ->
        let compile_args = List.concat (List.map (compile_expr) (List.rev args)) in
        compile_args @ [CALL (f, List.length args, false)], false, lb

    | Language.Stmt.Return expr -> (match expr with
                                    | Some x -> (compile_expr x) @ [RET true]
                                    | _ -> [RET false]), false, lb


(* SM compiler itself *)
let rec compile (defs, main) =

    let top_compile lb p =
            let lb, label = lb#get_label in
            let prg, used, lb = compile_impl lb p label in
            lb, prg @ (if used then [LABEL label] else [])
    in

    let compile_defs lb defs =
        List.fold_left (fun (lb, prg) (name, (args, locals, body)) ->
            let (lb, body) = top_compile lb body in
            lb, prg @ [LABEL name] @ [BEGIN (name, args, locals)] @ body @ [END]) (lb, []) defs
    in

    let lb = new labels in
    let lb, main = top_compile lb main in
    let lb, defs = compile_defs lb defs in
    main @ [END] @ defs
