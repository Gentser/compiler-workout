(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option

    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns resulting configuration
    *)
    (* let rec eval env ((st, i, o, r) as conf) expr = failwith "Not implemented" *)
    let boolToInt b = if b then 1 else 0

    let intToBool i = i != 0

    let fun1 op = fun x1 x2 -> boolToInt(op x1 x2)
    let fun2 op = fun x1 x2 -> boolToInt (op (intToBool x1) (intToBool x2))

    let to_func op =
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

    let rec eval state exp = match exp with
       | Const n -> n
       | Var x -> State.eval state x
       | Binop (op, x1, x2) -> to_func op (eval state x1) (eval state x2)

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
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment is the same as for expressions
    *)
    (* let rec eval env ((st, i, o, r) as conf) k stmt = failwith "Not implemnted" *)
    let reverseCondition c = Expr.Binop ("==", c, Expr.Const 0)
    let headToTail t m = match t with
        | head::tail -> (head, tail)
        | _ -> failwith(m)

    let rec eval env ((s, i, o) as config) p = match p with
        (* <s, i, o> --> <s[ x<-[|e|]s ], i, o> *)
        | Assign (name, e)          -> (State.update name (Expr.eval s e) s, i, o)
        (* <s, z::i, o> --> <s[x<-z], i, o> *)
        | Read name                 -> let (head, tail) = headToTail i "Unexpected end of input (no info)" in
                                       (State.update name head s, tail, o)
        (* <s, i, o> --> <s, i, o @ [ [|e|]s ]> *)
        | Write e                   -> (s, i, o @ [Expr.eval s e])
        (* C1 -S1-> C' -S2-> C2*)
        | Seq (e1, e2)              -> let (s1, i1, o1) = eval env config e1 in
                                       eval env (s1, i1, o1) e2

        | Skip                      -> config
        | If (cond, thn, els)       -> let cv = Expr.eval s cond in
                                       if cv <> 0 then
                                           eval env config thn
                                       else
                                           eval env config els

        | While (cond, body)        -> let cv = Expr.eval s cond in
                                       if cv == 0 then config
                                       else
                                           let c' = eval env config body in
                                           eval env c' (While (cond, body))

        | Repeat (body, cond)       -> let c' = eval env config body in
                                       eval env c' (While (reverseCondition cond, body))

        | Call (name, args)         -> let (arg_names, locals, body) = env#definition name in
                                       let fun_state = State.push_scope s (arg_names @ locals) in
                                       let args_values = List.map (Expr.eval s) args in
                                       let fun_env_w_args =
                                           List.fold_left (fun s (name, value) -> State.update name value s) fun_state
                                                          (List.combine arg_names args_values) in
                                       let (s', i', o') = eval env (fun_env_w_args, i, o) body in
                                       ((State.drop_scope s' s), i', o');;

    (* Statement parser *)
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
                Repeat (body, cond)
            }
            | name:IDENT "(" args:(!(Expr.parse))* ")"
            {
                Call (name, args)
            }
            | "skip" {Skip}
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse: "fun" name:IDENT "(" args:(IDENT)* ")"
             local:(%"local" (IDENT)*)?
             "{" body:!(Stmt.parse) "}"
             {
                 let local = match local with
                    | Some x -> x
                    | _ -> [] in
                 name, (args, local, body)
             }
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      =  snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
