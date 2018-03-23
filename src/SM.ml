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
<<<<<<< HEAD
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
=======

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env conf prog = failwith "Not yet implemented"
>>>>>>> 88cd6eaa4b79add3d179d7b5646f99b73460ad12

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes an input stream, a program, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Expr.empty, i, [])) p in o

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes an input stream, a program, and returns an output stream this program calculates
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
<<<<<<< HEAD
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
=======
*)
let compile p = failwith "Not yet implemented"
>>>>>>> 88cd6eaa4b79add3d179d7b5646f99b73460ad12
