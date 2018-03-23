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

    let rec eval stat expr = 
      match expr with
      | Const c -> c
      | Var v -> stat v
      | Binop (op, a, b) -> 
        let x = eval stat a and y = eval stat b in
        eval_binop op x y

    (* Expression parser. You can use the following terminals:
         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
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
    (* loop with a post-condition       *) | Repeat of t * Expr.t  with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator
         val eval : config -> t -> config
       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval ((st, i, o) as config) stmt =
      match stmt with
      | Assign (x, e) -> ((Expr.update x (Expr.eval st e) st), i, o)
      | Read x -> (
        match i with 
        | z :: i_tail -> ((Expr.update x z st), i_tail, o)
        | [] -> failwith "[READ]: Empty input stream"
      )
      | Write e -> (st, i, o @ [(Expr.eval st e)])
      | Seq (a, b) -> 
        let a_conf = eval (st, i, o) a in
        eval a_conf b
      | Skip -> config
      | If (cond, the, els) -> eval config (if Expr.eval st cond == 1 then the else els)
      | While (cond, body) -> 
        let rec while_loop ((st', _, _) as config') = 
          if (Expr.eval st' cond != 0)
          then while_loop (eval config' body)
          else config'
        in while_loop config
      | Repeat (body, until_cond) -> 
        let rec repeat_loop ((st', _, _) as config') =
          let ((st'', _, _) as config'') = eval config' body in 
          if (Expr.eval st'' until_cond == 0)
          then repeat_loop config''
          else config''
        in repeat_loop config
                               
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
      parse: !(Ostap.Util.expr
        (fun x -> x)
        [|
          `Righta, [ostap(";"), fun a b -> Seq(a, b)];
        |]
        primary
      );
      primary: 
          %"read" "(" x:IDENT ")"                             { Read  x }
        | %"write" "(" e: !(Expr.parse) ")"                   { Write e }
        | x:IDENT -":=" e: !(Expr.parse)                      { Assign (x, e) }
        | %"skip"                                             { Skip }
        | %"if" cond: !(Expr.parse) %"then" act:parse
          elif_acts:(%"elif" !(Expr.parse) %"then" parse)*
          els_act:(%"else" parse)?
          %"fi"                                               { If (cond, act, parse_elif_else elif_acts els_act) }
        | %"while" cond: !(Expr.parse) %"do" act:parse %"od"  { While (cond, act) }
        | %"repeat" act:parse %"until" cond: !(Expr.parse)    { Repeat (act, cond) }
        | %"for" init:parse "," cond: !(Expr.parse)
          "," inc:parse %"do" act:parse %"od"                 { Seq (init, While (cond, Seq (act, inc))) }
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
