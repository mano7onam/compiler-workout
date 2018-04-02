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
    type t = { g: string -> int; l: string -> int; scope: string list }

    let make_empty_state x = failwith (Printf.sprintf "Undefined variable %s" x)

    (* Empty state *)
    let empty = { g = make_empty_state; l = make_empty_state; scope = [] }

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    (* update l or g depends on x in or not in scope *)
    let update x v s =
      let update_fun f y = if x = y then v else f y
      in 
      if List.mem x s.scope
      then { g = s.g; l = update_fun s.l; scope = s.scope }
      else { g = update_fun s.g; l = s.l; scope = s.scope }

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = if List.mem x s.scope then (s.l x) else (s.g x)

    (* Creates a new scope, based on a given state *)
    (* xs - is list of locals *)
    let enter st xs = { g = st.g; l = make_empty_state; scope = xs }

    (* Drops a scope *)
    let leave st st' = { g = st'.g; l = st.l; scope = st.scope }

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
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    let rec eval_binop op x y =
      match op with
      | "+" -> x + y
      | "-" -> x - y
      | "*" -> x * y
      | "/" -> x / y
      | "%" -> x mod y
      | "&&" -> if x == 0 || y == 0 then 0 else 1
      | "!!" -> if x == 0 && y == 0 then 0 else 1
      | "<" -> if x < y then 1 else 0
      | "<=" -> if x <= y then 1 else 0
      | ">" -> if x > y then 1 else 0
      | ">=" -> if x >= y then 1 else 0
      | "==" -> if x == y then 1 else 0
      | "!=" -> if x != y then 1 else 0
      | _ -> failwith "[EVAL_BINOP]: Unknown binary operator"

    (* Expression evaluator
          val eval : state -> t -> int
       Takes a state and an expression, and returns the value of the expression in
       the given state.
    *)
    let rec eval stat expr = 
      match expr with
      | Const c -> c
      | Var v -> State.eval stat v
      | Binop (op, a, b) -> 
        let x = eval stat a and y = eval stat b in
        eval_binop op x y
    
    (* Expression parser. You can use the following terminals:
         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as an int
    *)
    let make_parser_ops ops = List.map (fun op -> ostap ($(op)), fun a b -> Binop(op, a, b)) ops

    ostap (
      parse: !(Ostap.Util.expr
        (fun x -> x)
        [|
          `Lefta, make_parser_ops ["!!"];
          `Lefta, make_parser_ops ["&&"];
          `Nona , make_parser_ops [">="; ">"; "<="; "<"; "=="; "!="];
          `Lefta, make_parser_ops ["+"; "-"];
          `Lefta, make_parser_ops ["*"; "/"; "%"];
        |]
        primary
      );
      primary: 
          v:IDENT   {Var v} 
        | c:DECIMAL {Const c} 
        | -"(" parse -")"
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
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list

    (* Statement evaluator
         val eval : env -> config -> t -> config
       Takes an environment, a configuration and a statement, and returns another configuration. The
       environment supplies the following method
           method definition : string -> (string list, string list, t)
       which returns a list of formal parameters, local variables, and a body for given definition
    *)
    let rec eval env ((st, i, o) as config) stmt =
      match stmt with
      | Assign (x, e) -> ((State.update x (Expr.eval st e) st), i, o)
      | Read x -> 
        let z :: i_tail = i 
        in ((State.update x z st), i_tail, o)
      | Write e -> (st, i, o @ [(Expr.eval st e)])
      | Seq (a, b) -> 
        let a_conf = eval env (st, i, o) a in
        eval env a_conf b
      | Skip -> config
      | If (cond, the, els) -> eval env config (if Expr.eval st cond == 1 then the else els)
      | While (cond, body) -> 
        let rec while_loop ((st', _, _) as config') = 
          if (Expr.eval st' cond != 0)
          then while_loop (eval env config' body)
          else config'
        in while_loop config
      | Repeat (body, until_cond) -> 
        let rec repeat_loop ((st', _, _) as config') =
          let ((st'', _, _) as config'') = eval env config' body in 
          if (Expr.eval st'' until_cond == 0)
          then repeat_loop config''
          else config''
          in repeat_loop config
      | Call (f, exprs)  ->
        let args, vars, body = env#definition f
        in let do_assign_arg stat (x, e) = State.update x (Expr.eval st e) stat (* update state x = e *)
        in let do_enter = State.enter st @@ args @ vars (* set scope args @ vargs *)
        in let rec zip = function
        | x::xs, y::ys -> (x, y) :: zip (xs, ys)
        | [], []       -> []
        in let assigned_state = List.fold_left do_assign_arg do_enter @@ zip (args, exprs)
        in let st', i, o = eval env (assigned_state, i, o) body
        in State.leave st st', i, o

    (* Statement parser *)
    let rec parse_elif_acts elif_acts parsed_else_act = 
      match elif_acts with
      [] -> parsed_else_act
      | (cond, act)::tail -> If (cond, act, parse_elif_acts tail parsed_else_act)

    let parse_elif_else elif_acts else_act = 
      let parsed_else_act = 
        match else_act with
        | None -> Skip
        | Some act -> act
      in parse_elif_acts elif_acts parsed_else_act

    ostap (
      parse:
          a:primary ";" b:parse { Seq (a, b) }
        | primary;

      expr: !(Expr.parse) ;

      function_s: hd:expr tl:((-"," expr)* ) { hd :: tl } | empty { [] } ;

      primary:
          %"read" "(" x:IDENT ")"                             { Read  x }
        | %"write" "(" e: !(Expr.parse) ")"                   { Write e }
        | x:IDENT ":=" e: !(Expr.parse)                       { Assign (x, e) }
        | %"skip"                                             { Skip }
        | %"if" cond: !(Expr.parse) %"then" act:parse
          elif_acts:(%"elif" !(Expr.parse) %"then" parse)*
          els_act:(%"else" parse)?
          %"fi"                                               { If (cond, act, parse_elif_else elif_acts els_act) }
        | %"while" cond: !(Expr.parse) %"do" act:parse %"od"  { While (cond, act) }
        | %"repeat" act:parse %"until" cond: !(Expr.parse)    { Repeat (act, cond) }
        | %"for" init:parse "," cond: !(Expr.parse)
          "," inc:parse %"do" act:parse %"od"                 { Seq (init, While (cond, Seq (act, inc))) }
        | f:IDENT "(" args:function_s ")"                       { Call (f, args) }
    )

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      parse: %"fun" name:IDENT "(" args:(ids | nothing) ")" vars:(-(%"local") ids | nothing)
        "{" body:stmt "}" { name, (args, vars, body) } ;

      stmt: !(Stmt.parse) ;

      nothing: empty { [] } ;

      ids: hd:IDENT tl:((-"," IDENT)* ) { hd :: tl }
    )

  end

(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t

(* Top-level evaluator
     eval : t -> int list -> int list
   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, stmt) i =
  let module M = Map.Make (String)
  in let defs_map = List.fold_left (fun m (f, data) -> M.add f data m) M.empty defs
  in let env_obj = (object method definition f = M.find f defs_map end)
  in let _, _, output = Stmt.eval env_obj (State.empty, i, []) stmt
  in output

(* Top-level parser *)
ostap (
  defs: !(Definition.parse) * ;

  parse: pre_defs:defs stmt:!(Stmt.parse) post_defs:defs { pre_defs @ post_defs, stmt }
)