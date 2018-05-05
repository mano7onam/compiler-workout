open GT       
open Language
open List
       
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

  let check_cond_jmp cond value = 
    match cond with
    | "nz" -> Value.to_int value <> 0
    | "z" -> Value.to_int value = 0 

let rec resolve_argument_mapping accumulator args stack = 
  match args, stack with
  | [], _ -> List.rev accumulator, stack
  | a::tail_args, s::tail_stack -> resolve_argument_mapping ((a, s)::accumulator) tail_args tail_stack
        
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prog_tail ->
    (
      match insn with
      | BINOP op -> 
        let y::x::stack' = stack in
        let res = Expr.eval_binop op (Value.to_int x) (Value.to_int y) in
        eval env (cstack, (Value.of_int res) :: stack', c) prog_tail

      | CONST z  -> 
        eval env (cstack, (Value.of_int z)::stack, c) prog_tail

      | STRING s -> 
        eval env (cstack, (Value.of_string s)::stack, c) prog_tail

      | LD x -> 
        eval env (cstack, State.eval st x :: stack, c) prog_tail

      | ST x -> 
        let z::stack' = stack in 
        eval env (cstack, stack', (State.update x z st, i, o)) prog_tail

      | STA (x, n) -> 
        let v::ind, stack' = split (n + 1) stack in 
        eval env (cstack, stack', (Language.Stmt.update st x v (List.rev ind), i, o)) prog_tail

      | LABEL s  -> eval env conf prog_tail

      | JMP label -> eval env conf (env#labeled label)

      | CJMP (cond, label) -> 
        eval env (cstack, tl stack, c) 
        (
          if (check_cond_jmp cond (hd stack)) 
          then (env#labeled label) 
          else prog_tail
        )

      | CALL (fname, n, p) -> 
        if env#is_label fname
        then eval env ((prog_tail, st)::cstack, stack, c) (env#labeled fname) 
        else eval env (env#builtin conf fname n p) prog_tail

      | BEGIN (_, args, xs) ->
        let rec init_args st = function
          | a::args, z::stack -> 
            let state', stack' = init_args st (args, stack) in 
            State.update a z state', stack'
          | [], stack -> st, stack
        in let state', stack' = init_args (State.enter st @@ args @ xs) (args, stack)
        in eval env (cstack, stack', (state', i, o)) prog_tail

      | END | RET _ -> 
        (
          match cstack with
          | (prog_tail, st')::cstack' -> eval env (cstack', stack, (State.leave st st', i, o)) prog_tail
          | [] -> conf
        )
    )

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
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

class labels = 
  object (self)
    val counter = 0
    method new_label = "label_" ^ string_of_int counter, {<counter = counter + 1>}
  end 

let func_label name = "L" ^ name

let rec compile_body labels =
  let rec compile_expr = function
  | Expr.Var x -> [LD x]
  | Expr.Const n -> [CONST n]
  | Expr.Binop (op, x, y) -> compile_expr x @ compile_expr y @ [BINOP op]
  | Expr.String s -> [STRING s]
  | Expr.Array arr -> List.flatten (List.map compile_expr arr) @ [CALL ("$array", List.length arr, false)]
  | Expr.Length t -> compile_expr t @ [CALL ("$length", 1, false)]
  | Expr.Elem (arr, i) -> compile_expr arr @ compile_expr i @ [CALL ("$elem", 2, false)]
  | Expr.Call (f, args) -> compile_call f args false
  and compile_call f args p = 
    let compiled_arglist = List.map compile_expr (List.rev args) in
    let compiled_args = List.concat compiled_arglist in
    compiled_args @ [CALL (func_label f, List.length args, p)]
  in
  function
  | Stmt.Seq (a, b) -> 
    let labelsa, resa = compile_body labels a in
    let labelsb, resb = compile_body labelsa b in
    labelsb, resa @ resb

  | Stmt.Assign (x, [], e) -> labels, compile_expr e @ [ST x]

  | Stmt.Assign (x, is, e) -> labels, List.flatten (List.map compile_expr (is @ [e])) @ [STA (x, List.length is)]

  | Stmt.Skip -> labels, []

  | Stmt.If (cond, then_body, else_body) ->
    let compiled_cond = compile_expr cond in
    let label_else, labels1 = labels#new_label in
    let label_endif, labels2 = labels1#new_label in
    let labels3, compiled_if = compile_body labels2 then_body in
    let labels4, compiled_else = compile_body labels3 else_body in
    labels4, compiled_cond @ 
    [CJMP ("z", label_else)] @ 
    compiled_if @ 
    [JMP label_endif] @ 
    [LABEL label_else] @ 
    compiled_else @ 
    [LABEL label_endif]

  | Stmt.While (cond, while_body) ->
    let compiled_cond = compile_expr cond in
    let label_begin, labels1 = labels#new_label in
    let label_end, labels2 = labels1#new_label in
    let labels3, compiled_while_body = compile_body labels2 while_body in
    labels3, 
    [LABEL label_begin] @ 
    compiled_cond @ 
    [CJMP ("z", label_end)] @ 
    compiled_while_body @ 
    [JMP label_begin] @ 
    [LABEL label_end] 

  | Stmt.Repeat (repeat_body, cond) ->
    let compiled_cond = compile_expr cond in
    let label_begin, labels1 = labels#new_label in
    let labels2, compiled_loop_body = compile_body labels1 repeat_body in
    labels2, 
    [LABEL label_begin] @ 
    compiled_loop_body @ 
    compiled_cond @ 
    [CJMP ("z", label_begin)]

  | Stmt.Call (f, args) -> 
    labels, compile_call f args true
    
  | Stmt.Return res -> 
    labels, 
    (
      match res with 
      None -> [] 
      | Some v -> compile_expr v
    ) 
    @ [RET (res <> None)]

let compile_fun_def labels (fun_name, (args, locals, body)) = 
  let end_label, labels1 = labels#new_label in
  let labels2, compiled_fun = compile_body labels1 body in
  labels2, 
  [LABEL fun_name; BEGIN (fun_name, args, locals)] @ compiled_fun @ [LABEL end_label; END]

let compile_all_defs labels defs = 
  List.fold_left 
  (
    fun (labels, compiled_all_fun_defs) (fun_name, other_fun_names) -> 
    let labels1, compiled_single_fun = compile_fun_def labels (func_label fun_name, other_fun_names) in 
    labels1, compiled_single_fun::compiled_all_fun_defs
  )
  (labels, []) defs

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = let end_label, labels = (new labels)#new_label in
  let labels1, compiled_prog = compile_body labels p in 
  let labels2, compiled_all_fun_defs = compile_all_defs labels1 defs in
  (compiled_prog @ [LABEL end_label]) @ [END] @ (List.concat compiled_all_fun_defs)