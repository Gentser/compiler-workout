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

    let rec eval env ((s, i, o, r) as conf) expr = match expr with
       | Const n -> (s, i, o, Some n)
       | Var x -> (s, i, o, Some (State.eval s x))
       | Binop (op, x1, x2) -> let (s, i, o, Some r1) = eval env conf x1 in
                               let (s, i, o, Some r2) = eval env (s, i, o, None) x2 in
                               (s, i, o, Some (to_func op r1 r2))
       | Call (func, args) -> let (s, i, o, args) =
                              List.fold_left (fun (s, i, o, args) arg ->
                                  let (s, i, o, Some res) = eval env (s, i, o, None) arg in
                                  (s, i, o, args @ [res])) (s, i, o, []) args in
                                  env#definition env func args (s, i, o, None)
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
      	primary: c:DECIMAL {Const c}
               | name:IDENT p:("(" args:!(Util.list0 parse) ")" {Call (name, args)} | empty {Var name}) {p}
               | -"(" expr -")"  (* simpiest expression - {var, const, (var), (const)}*)
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

    let meta x y = match x with
        | Skip -> y
        | _ -> match y with
            | Skip -> x
            | _ -> Seq (x, y)

    let rec eval env ((s, i, o, _) as config) k p = match p with
        (* <s, i, o> --> <s[ x<-[|e|]s ], i, o> *)
        | Assign (name, e)          -> let (s, i, o, Some r) = Expr.eval env config e in
                                       eval env (State.update name r s, i, o, Some r) Skip k
        (* <s, z::i, o> --> <s[x<-z], i, o> *)
        | Read name                 -> let (head, tail) = headToTail i "Unexpected end of input (no info)" in
                                       eval env (State.update name head s, tail, o, None) Skip k
        (* <s, i, o> --> <s, i, o @ [ [|e|]s ]> *)
        | Write e                   -> let (s, i, o, Some r) = Expr.eval env config e in
                                       eval env (s, i, o @ [r], None) Skip k
        (* C1 -S1-> C' -S2-> C2*)
        | Seq (e1, e2)              -> eval env config (meta e2 k) e1

        | Skip                      -> (match k with
                                          | Skip -> config
                                          | _ -> eval env config Skip k)
        | If (cond, thn, els)       -> let ((s, i, o, Some cond_value) as c) = Expr.eval env config cond in
                                       if cond_value <> 0 then
                                          eval env c k thn
                                       else
                                          eval env c k els

        | While (cond, body)        -> let ((s, i, o, Some cond_value) as c) = Expr.eval env config cond in
                                       if cond_value == 0 then eval env c Skip k
                                       else eval env c (meta p k) body

        | Repeat (body, cond)       -> eval env config (meta (While (reverseCondition cond, body)) k) body

        | Call (name, args)         -> eval env (Expr.eval env config (Expr.Call (name, args))) Skip k
        | Return x                  -> (match x with
                                          | Some x -> Expr.eval env config x
                                          | _ -> config);;

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
            | name:IDENT "(" args:!(Util.list0 Expr.parse) ")"
            {
                Call (name, args)
            }
            | "skip" {Skip}
            | "return" expr:!(Expr.parse)? { Return expr }
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    (* Auxiliary function *)
    let option_to_list x = match x with
      | Some y -> y
      | None -> []

    ostap (
      arg: IDENT;
      parse: "fun" name:IDENT "(" args:!(Util.list0 arg) ")"
             local:(%"local" !(Util.list arg))?
             "{" body:!(Stmt.parse) "}"
             {
                 name, (args, option_to_list(local), body)
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
