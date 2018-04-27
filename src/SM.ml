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

(* Stack machine interpreter
     val eval : env -> config -> prg -> config
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let check_cond_jmp cond value = 
  match cond with
  | "nz" -> value <> 0
  | "z" -> value = 0 

let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval env conf = function
  | [] -> conf
  | instr::prog_tail ->
    let (cstack, stack, stmt_conf) = conf in
    let (st, i, o) = stmt_conf in
    match instr with
    | BINOP op ->
      let (x::y::stack_tail) = stack in
      let res = Expr.eval_binop op y x in
      eval env (cstack, res::stack_tail, stmt_conf) prog_tail
    | CONST z -> eval env (cstack, z::stack, stmt_conf) prog_tail
    | READ -> 
      let (i::i_tail) = i in 
      eval env (cstack, i::stack, (st, i_tail, o)) prog_tail
    | WRITE -> 
      let (z::stack_tail) = stack in 
      eval env (cstack, stack_tail, (st, i, o @ [z])) prog_tail
    | LD x -> 
      let res = State.eval st x in
      eval env (cstack, res::stack, stmt_conf) prog_tail
    | ST x -> 
      let (s::stack_tail) = stack in
      let res = State.update x s st in
      eval env (cstack, stack_tail, (res, i, o)) prog_tail
    | LABEL _ -> eval env conf prog_tail
    | JMP label -> eval env conf (env#labeled label)
    | CJMP (cond, label)  -> 
      (
			  eval env (cstack, List.tl stack, stmt_conf)
        (if (check_cond_jmp cond (List.hd stack)) then (env#labeled label) else prog_tail)
      )
    | CALL (f, _, _) -> eval env ((prog_tail, st)::cstack, stack, stmt_conf) @@ env#labeled f
    | BEGIN (_, args, xs) ->
      let rec init_args st = function
        | a::args, z::stack -> 
          let state', stack' = init_args st (args, stack) in 
          State.update a z state', stack'
        | [], stack -> st, stack
      in let state', stack' = init_args (State.enter st @@ args @ xs) (args, stack)
      in eval env (cstack, stack', (state', i, o)) prog_tail
    | END | RET _ ->
      match cstack with
      | (prog, s)::cstack' ->
        let res = State.leave st s, i, o in
        eval env (cstack', stack, res) prog
      | [] -> conf

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

(* Stack machine compiler
     val compile : Language.t -> prg
   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let rec compile_expr = function
  | Expr.Var x -> [LD x]
  | Expr.Const n -> [CONST n]
  | Expr.Binop (op, x, y) -> 
    compile_expr x @ 
    compile_expr y @ 
    [BINOP op]
  | Expr.Call (fun_name, args) -> 
    List.fold_left (fun ac e -> compile_expr e @ ac) [] args @ 
    [CALL (fun_name, List.length args, false)]

let compile (defs, prog) = 
  let env = object 
    val mutable id = 0
    method generate = 
      id <- (id + 1);
      "L" ^ string_of_int id
  end
  in let rec compile_body prog =
    match prog with
    | Stmt.Assign (x, e) -> (compile_expr e) @ [ST x]
    | Stmt.Read x -> [READ] @ [ST x]
    | Stmt.Write e -> (compile_expr e) @ [WRITE]
    | Stmt.Seq (a, b) -> (compile_body a) @ (compile_body b)
    | Stmt.Skip -> []
    | Stmt.If (cond, then_body, else_body) ->
      let compiled_cond = compile_expr cond in
      let label_else = env#generate in 
      let label_end_if = env#generate in
      let then_compiled = compile_body then_body in
      let else_compiled = compile_body else_body in
      compiled_cond @ 
      [CJMP ("z", label_else)] @ 
      then_compiled @ 
      [JMP label_end_if; LABEL label_else] @ 
      else_compiled @ 
      [LABEL label_end_if]
    | Stmt.While (cond, while_body) ->
      let compiled_cond = compile_expr cond in
      let label_cond = env#generate in
      let label_loop = env#generate in
      let compiled_while_body = compile_body while_body in
      [JMP label_cond; LABEL label_loop] @ 
      compiled_while_body @ 
      [LABEL label_cond] @ 
      compiled_cond @ 
      [CJMP ("nz", label_loop)]
    | Stmt.Repeat (cond, repeat_body) ->
      let label_loop= env#generate in
      let compiled_repeat_body = compile_body repeat_body in
      [LABEL label_loop] @ 
      compiled_repeat_body @ 
      compile_expr cond @ 
      [CJMP ("z", label_loop)]
    | Stmt.Return e -> 
      (
        match e with
        | None -> [RET false]
        | Some e -> compile_expr e @ [RET true]
      )
    | Stmt.Call (fun_name, args) -> 
      List.concat (List.map compile_expr args) @ 
      [CALL (fun_name, List.length args, true)] in
      let compile_def (fun_name, (args, locals, body)) = 
        [
          LABEL fun_name; 
          BEGIN (fun_name, args, locals)
        ] 
        @ compile_body body @ [END] 
      in
	  (compile_body prog @ [END] @ List.concat (List.map compile_def defs))
