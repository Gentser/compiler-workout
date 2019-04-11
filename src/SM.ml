open GT
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

let insn_string = function
| BINOP op  -> Printf.sprintf "BINOP %s" op
| CONST c   -> Printf.sprintf "CONST %d" c
| STRING s  -> Printf.sprintf "STRING %s" s
| LD s      -> Printf.sprintf "LD %s" s
| ST s      -> Printf.sprintf "ST %s" s
| STA (s, i) -> Printf.sprintf "STA %s %d" s i
| LABEL s -> Printf.sprintf "LABEL %s" s
| JMP s -> Printf.sprintf "JMP %s" s
| CJMP (cond, x) -> Printf.sprintf "CJMP %s" cond
| BEGIN (name, args, locals) -> Printf.sprintf "BEGIN %s ..." name
| END -> Printf.sprintf "END"
| CALL (name, argc, isFun) -> Printf.sprintf "CALL %s %n" name argc
| RET b -> Printf.sprintf "RET %b" b

let print_program prg =
List.fold_left (fun _ insn -> Printf.printf "%s;\n" (insn_string insn)) () prg;
Printf.printf "\n"

let rec print_stack = function
| [] -> Printf.printf "\n"
| z::stack' ->
  match z with
  | Value.Int i -> Printf.printf "%d; " i
  | Value.String s -> Printf.printf "%s; " s;
  | Value.Array _ -> Printf.printf "array...; ";
  print_stack stack'

(* Stack machine interpreter
     val eval : env -> config -> prg -> config
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prg' ->
  (*Printf.printf "Evaluating %s...\n" (insn_string insn); (* DEBUG *)*)
  eval env (
    match insn with
    | BINOP op -> let y::x::stack' = stack in (cstack, Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y)) :: stack', c)
    | CONST i -> (cstack, (Value.of_int i)::stack, c)
    | STRING s -> (cstack, (Value.of_string s)::stack, c)
    | LD x -> (cstack, (State.eval st x) :: stack, c)
    | ST x -> let z::stack' = stack in (cstack, stack', (State.update x z st, i, o))
    | STA (x, n) ->
      let (z::args, stack') = split (n + 1) stack
      in (cstack, stack', (Stmt.update st x z args, i, o))
    | LABEL _ -> conf
    | JMP _ -> conf
    | CJMP (cond, l) -> let z::stack' = stack in (cstack, stack', c)
    | BEGIN (_, args, ls) ->
      let inner_st = State.enter st (args @ ls) in
      let st', stack' = List.fold_left (fun (s, (z :: stck)) x -> State.update x z s, stck) (inner_st, stack) args in
      (cstack, stack', (st', i, o))
    | END | RET _    ->
      (match cstack with
      | [] -> conf
      | (_, s) :: cstack' -> (cstack', stack, (State.leave st s, i, o))
      )
    | CALL (name, argc, isFun) ->
      if env#is_label name
      then ((prg', st)::cstack, stack, c)
      else (env#builtin conf name argc isFun)
  )
   (let cjmp_cond cond x =
      match cond with
      | "z"  -> x = 0
      | "nz" -> x <> 0
      | _    -> failwith "Unexpected cjump parameter"
    in
      match insn with
      | JMP l             -> env#labeled l
      | CJMP (cond, l)    -> let z::stack' = stack in (if cjmp_cond cond (Value.to_int z) then (env#labeled l) else prg')
      | CALL (name, _, _) -> if env#is_label name then env#labeled name else prg'
      | END | RET _       -> (match cstack with [] -> [] | (p, _) :: _ -> p)
      | _                 -> prg'
   )

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_program p (* DEBUG *)*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if (not p) then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
class label_generator =
  object (self)
    val cntr = 2
    method create =
      let str = string_of_int cntr
      in ".L"^str, {<cntr = cntr + 1>}
end

let rec compile' labgen =
  let rec expr = function
  | Expr.Const n          -> [CONST n]
  | Expr.Array es         -> exprList (List.rev es) @ [CALL ("$array", List.length es, true)]
  | Expr.String s         -> [STRING s]
  | Expr.Var x            -> [LD x]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Elem (b, j)      -> expr b @ expr j @ [CALL ("$elem", 2, true)]
  | Expr.Length v         -> expr v @ [CALL ("$length", 1, true)]
  | Expr.Call (f, es)     -> exprList es @ [CALL (f, List.length es, true)]
  and exprList es = List.fold_left (fun acc e -> expr e @ acc) [] es
  in function
  | Stmt.Assign (x, [], e) -> labgen, expr e @ [ST x]
  | Stmt.Assign (x, ks, e) -> labgen, exprList ks @ expr e @ [STA (x, List.length ks)]
  | Stmt.Seq (s1, s2)  ->
      let labgen, compiled_s1 = compile' labgen s1 in
      let labgen, compiled_s2 = compile' labgen s2 in
      labgen, compiled_s1 @ compiled_s2
  | Stmt.Skip              -> labgen, []
  | Stmt.If (c, s, es) ->
      let else_label, labgen = labgen#create in
      let endif_label, labgen = labgen#create in
      let labgen, compiled_s = compile' labgen s in
      let labgen, compiled_es = compile' labgen es in
      labgen,
      expr c @ [CJMP("z", else_label)]
        @ compiled_s @ [JMP endif_label; LABEL else_label]
        @ compiled_es
        @ [LABEL endif_label]
  | Stmt.While (c, s)  ->
      let while_label, labgen = labgen#create in
      let endwhile_label, labgen = labgen#create in
      let labgen, compiled_s = compile' labgen s in
      labgen,
      [LABEL while_label] @ expr c @ [CJMP("z", endwhile_label)]
      @ compiled_s @ [JMP while_label; LABEL endwhile_label]
  | Stmt.Repeat (s, c) ->
      let repeat_label, labgen = labgen#create in
      let labgen, compiled_s = compile' labgen s in
      labgen,
      [LABEL repeat_label] @ compiled_s @ (expr c) @ [CJMP("z", repeat_label)]
  | Stmt.Call (name, args) ->
      let compiled_args = List.fold_left (fun ilist arg -> ilist @ (expr arg)) [] args in
      labgen, compiled_args @ [CALL (name, List.length args, false)]
  | Stmt.Return optexpr    ->
      labgen,
        (match optexpr with Some e -> expr e | None -> []) @
        [RET (match optexpr with Some _ -> true | None -> false)]

let compile_proc labgen (name, (argnames, locals, body)) =
  let labgen, compiled_body = compile' labgen body in
  labgen, [LABEL (name); BEGIN (name, argnames, locals)] @ compiled_body @ [END]

let compile (defs, p) =
  let labgen, compiled_defs = List.fold_left
    (fun (lg, ilist) def ->
      let (lg', proc_ilist) = compile_proc lg def in (lg', ilist @ proc_ilist))
    (new label_generator, []) defs in
  let (_, compiled_s) = compile' labgen p in
  compiled_s @ [END] @ compiled_defs
