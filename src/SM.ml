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
let perform_inst inst ((st, (s, i, o)) : config) = 
  match inst with
  | BINOP op -> (
    match st with 
    | y :: x :: st_tail -> ((Language.Expr.eval_binop op x y) :: st_tail, (s, i ,o)) 
    | _ -> failwith "[BINOP]: Too few arguments on stack"		
  )
  | CONST n -> (n :: st, (s, i, o))
  | READ -> (
    match i with
    | z :: i_tail -> (z :: st, (s, i_tail, o))
    | _ -> failwith "[READ]: Too few arguments in input stream"
  )
  | WRITE -> (
    match st with
    | z :: st_tail -> (st_tail, (s, i, o @ [z]))
    | _ -> failwith "[WRITE]: Too few arguments on stack"
  )
  | LD x -> ((s x) :: st, (s, i, o))
  | ST x -> (
    match st with
    | z :: st_tail -> (st_tail, (Language.Expr.update x z s, i, o))
    | _ -> failwith "[ST]: Too few arguments on stack"
  )
                      
let rec eval conf prog = 
  match prog with
  | [] -> conf	
  | inst :: tail -> eval (perform_inst inst conf) tail

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile_expr (expr : Language.Expr.t) = 
  match expr with
  | Const n -> [CONST n]
  | Var x -> [LD x]
  | Binop (op, x, y) -> compile_expr x @ compile_expr y @ [BINOP op]

let rec compile (stmt : Language.Stmt.t) =
  match stmt with
  | Assign (x, e) -> (compile_expr e) @ [ST x]
  | Read x -> READ :: [ST x]
  | Write e -> (compile_expr e) @ [WRITE]
  | Seq (a, b) -> (compile a) @ (compile b)
