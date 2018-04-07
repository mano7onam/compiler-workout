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
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter
     val eval : env -> config -> prg -> config
   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let check_cond_jmp cond value = 
  match cond with
  | "nz" -> value <> 0
  | "z" -> value = 0 

let rec eval env conf = function 
	| [] -> conf
	| inst::prog -> 
		match inst, conf with
		| BINOP op, (cstack, y::x::stack_tail, stmt_conf) -> 
			let res = Expr.eval_binop op x y in
			eval env (cstack, res::stack_tail, stmt_conf) prog
		| CONST z, (cstack, stack, stmt_conf) ->
			eval env (cstack, z::stack, stmt_conf) prog
		| READ, (cstack, stack, (st, z::i, o)) ->
			eval env (cstack, z::stack, (st, i, o)) prog
		| WRITE, (cstack, z::stack, (st, i, o)) ->
			eval env (cstack, stack, (st, i, o @ [z])) prog
		| LD x, (cstack, stack, (st, i, o)) ->
			let res = State.eval st x 
			in 	eval env (cstack, res::stack, (st, i, o)) prog
		| ST x, (cstack, z::stack, (st, i, o)) ->
			let st' =	State.update x z st 
			in 	eval env (cstack, stack, (st', i, o)) prog
		| LABEL label, conf -> eval env conf prog
		| JMP label, conf -> eval env conf (env#labeled label)
		| CJMP (cond, label), (cstack, stack, stmt_conf) -> (
			eval env (cstack, List.tl stack, stmt_conf)
      (if (check_cond_jmp cond (List.hd stack)) then (env#labeled label) else prog)
		)
		| CALL name, (cstack, stack, (st, i, o)) ->
			eval env ((prog, st)::cstack, stack, (st, i, o)) (env#labeled name)
		| BEGIN (args, xs), (cstack, stack, (st, i, o)) ->
			let rec init_args state = function
				| a::args, z::stack -> 
					let state', stack' = init_args state (args, stack)
					in State.update a z state', stack'
				| [], stack -> state, stack
			in let s', stack' = init_args (State.enter st @@ args @ xs) (args, stack)
			in eval env (cstack, stack', (s', i, o)) prog
		| END, (cstack, stack, (st, i, o)) -> 
		(
			match cstack with
			| (p', st')::cstack' -> 
				eval env (cstack', stack, (State.leave st st', i, o)) p'
			| [] -> conf
		)	

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
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
let rec compile_expr = function
| Expr.Var x -> [LD x]
| Expr.Const n -> [CONST n]
| Expr.Binop (op, x, y) -> 
  compile_expr x @ 
  compile_expr y @ 
	[BINOP op]
| Expr.Call (fun_name, args) ->
	List.concat (List.map compile_expr (List.rev args)) @ 
	[CALL fun_name]

let rec compile_body env = function
	| Stmt.Assign (x, e) -> compile_expr e @ [ST x], env
	| Stmt.Read x -> [READ; ST x], env
	| Stmt.Write e ->	compile_expr e @ [WRITE], env
	| Stmt.Seq (a, b) -> 
		let a', env = compile_body env a in
		let b', env = compile_body env b in
		a' @ b', env
	| Stmt.Skip -> [], env
	| Stmt.If (cond, then_body, else_body) ->
		let compiled_cond 			= compile_expr cond in
		let label_else, env 		= env#generate in 
		let label_end_if, env 	= env#generate in
		let then_compiled, env 	= compile_body env then_body in
		let else_compiled, env 	= compile_body env else_body in
		compiled_cond 												@ 
		[CJMP ("z", label_else)] 							@ 
		then_compiled 												@ 
		[JMP label_end_if; LABEL label_else] 	@ 
		else_compiled 												@ 
		[LABEL label_end_if], 
		env
	| Stmt.While (cond, while_body) ->
		let compiled_cond               		= compile_expr cond in
		let label_cond, env 								= env#generate in
		let label_loop, env 								= env#generate in
		let compiled_while_body, env 				= compile_body env while_body in
		[JMP label_cond; LABEL label_loop] 	@ 
		compiled_while_body 								@ 
		[LABEL label_cond] 									@ 
		compiled_cond 											@ 
		[CJMP ("nz", label_loop)], 
		env
	| Stmt.Repeat (cond, repeat_body) ->
		let label_loop, env 		= env#generate in
		let compiled_repeat_body, env = compile_body env repeat_body in
		[LABEL label_loop] 						@ 
		compiled_repeat_body 					@ 
		compile_expr cond 						@ 
		[CJMP ("z", label_loop)], 
		env
	| Stmt.Call (fun_name, args) ->
		List.concat (List.map compile_expr (List.rev args)) @ 
		[CALL fun_name], 
		env
	| Stmt.Return e ->
		match e with
		| None -> [END], env
		| Some e -> compile_expr e @ [END], env

let compile (defs, prog) = 
	let env = 
		object
    		val count_label = 0
    		method generate = "LABEL_" ^ string_of_int count_label, {< count_label = count_label + 1 >}
		end 
	in let compiled_prog, env = compile_body env prog
	in let rec compile_functions env def_functions =
		match def_functions with
		| (name, (args, locals, body))::def_functions' ->
			let rest_functions, env 	= compile_functions env def_functions' 
			in let compiled_body, env = compile_body env body
			in 
			[LABEL name; BEGIN (args, locals)] 		@ 
			compiled_body 												@ 
			[END] 																@ 
			rest_functions,
			env
		| [] -> [], env  
	in let all_functions, _  = compile_functions env defs 
	in 
	compiled_prog 	@ 
	[END] 					@ 
	all_functions