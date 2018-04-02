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
   Takes a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
 *)
 (* let eval env ((cstack, stack, ((st, i, o) as c)) as conf) = failwith "Not implemented" *)
let check_cond_jmp cond value = 
  match cond with
  | "nz" -> value <> 0
  | "z" -> value = 0 

let rec eval env ((cstack, stack, ((s, i, o) as conf)) as config) = function
  | [] -> config
  | inst :: prog ->
  (
    match inst with
    | BINOP op ->
      let y::x::stack_tail = stack 
      in eval env (cstack, (Expr.eval_binop op x y) :: stack_tail, conf) prog
    | CONST z -> eval env (cstack, z::stack, conf) prog
    | READ ->
      let z::i_tail = i 
      in eval env (cstack, z::stack, (s, i_tail, o)) prog
    | WRITE ->
      let z::stack_tail = stack
      in eval env (cstack, stack, (s, i, o @ [z])) prog
    | LD x -> eval env (cstack, (State.eval s x)::stack, conf) prog
    | ST x ->
      let z::stack_tail = stack 
      in eval env (cstack, stack, (State.update x z s, i, o)) prog
    | LABEL l -> eval env config prog
    | JMP label -> eval env config (env#labeled label)
    | CJMP (cond, label) -> 
      eval env (cstack, List.tl stack, conf)
      (if (check_cond_jmp cond (List.hd stack)) then (env#labeled label) else prog)
    | BEGIN (args, xs) ->
      let rec init_args state = function
        | a::args, z::stack -> 
          let state', stack' = init_args state (args, stack)
          in State.update a z state', stack'
        | [], stack -> state, stack
      in let s', stack' = init_args (State.enter s @@ args @ xs) (args, stack)
      in eval env (cstack, stack', (s', i, o)) prog
    | END -> 
      (
        match config with
        | (program, s)::cstack', stack, (s', i, o) ->
          eval env (cstack', stack, (State.leave s s', i, o)) program
        | _ -> config
      )
    | CALL f -> let cstack, stack, ((s, i, o) as conf) = config
      in eval env ((prog, s)::cstack, stack, conf) @@ env#labeled f
  )



(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String)
  in let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
 (* let compile (defs, p) = failwith "Not implemented" *)
class labels =
  object (self)
    val counter = 0
    method new_label = "label_" ^ string_of_int counter, {< counter = counter + 1 >}
end

let make_func_label name = "L" ^ name

let rec compile_expr = function
| Expr.Var x -> [LD x]
| Expr.Const n -> [CONST n]
| Expr.Binop (op, x, y) -> 
  compile_expr x @ 
  compile_expr y @ 
  [BINOP op]

let rec compile_labeled labels = function
  | Stmt.Assign (x, e) -> labels, compile_expr e @ [ST x]
  | Stmt.Read x        -> labels, [READ; ST x]
  | Stmt.Write e       -> labels, compile_expr e @ [WRITE]
  | Stmt.Seq (a, b) -> 
    let labels_a, prog_a = compile_labeled labels a in
    let labels_b, prog_b = compile_labeled labels_a b in
    labels_b, prog_a @ prog_b
  | Stmt.Skip -> labels, []
  | Stmt.If (cond, if_body, else_body) ->
    let compiled_cond             = compile_expr cond in
    let label_else, labels1       = labels#new_label in
    let label_end_if, labels2     = labels1#new_label in
    let labels3, compiled_if      = compile_labeled labels2 if_body in
    let labels4, compiled_else    = compile_labeled labels3 else_body in
    labels4, compiled_cond    @ 
    [CJMP ("z", label_else)]  @ 
    compiled_if               @ 
    [JMP label_end_if]        @ 
    [LABEL label_else]        @ 
    compiled_else             @ 
    [LABEL label_end_if]
  | Stmt.While (cond, loop_body) ->
    let compiled_cond                   = compile_expr cond in
    let label_begin, labels1            = labels#new_label in
    let label_end, labels2              = labels1#new_label in
    let labels3, compiled_loop_body     = compile_labeled labels2 loop_body in
    labels3, [LABEL label_begin]  @ 
    compiled_cond                 @ 
    [CJMP ("z", label_end)]       @ 
    compiled_loop_body            @ 
    [JMP label_begin]             @ 
    [LABEL label_end] 
  | Stmt.Repeat (loop_body, cond) ->
    let compiled_cond                   = compile_expr cond in
    let label_begin, labels1            = labels#new_label in
    let labels2, compiled_loop_body     = compile_labeled labels1 loop_body in
    labels2, [LABEL label_begin]  @ 
    compiled_loop_body            @ 
    compiled_cond                 @ 
    [CJMP ("z", label_begin)]
  | Stmt.Call (func_name, args) -> 
    let compiled_args_list = List.map compile_expr (List.rev args) in
    let compiled_args = List.concat compiled_args_list in
    labels, compiled_args @ [CALL (make_func_label func_name)]

let compile_function labels (func_name, (args, locals, body)) = 
  let end_label, labels1 = labels#new_label 
  in let labels2, compiled_function = compile_labeled labels1 body 
  in labels2, 
  [ LABEL func_name; BEGIN (args, locals) ] @ 
  compiled_function                         @ 
  [ LABEL end_label; END ]

let compile_all_functions labels all_functions = 
  List.fold_left 
  (
    fun (labels, functions) (func_name, func_signature) -> 
    let labels1, compiled_function = compile_function labels (make_func_label func_name, func_signature) 
    in  labels1, compiled_function :: functions
  )
  (labels, []) all_functions

(* Stack machine compiler
    val compile : Language.t -> prg
  Takes a program in the source language and returns an equivalent program for the
  stack machine
*)
let compile (defs, p) = let end_label, labels = (new labels)#new_label in
  let labels1, compiled_main_function = compile_labeled labels p in 
  let labels2, compiled_functions     = compile_all_functions labels1 defs in
  (LABEL "main" :: compiled_main_function @ [LABEL end_label]) @ 
  [END] @ 
  (List.concat compiled_functions)