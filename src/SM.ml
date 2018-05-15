open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
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
	| inst :: prog_tail -> 
	  let cfg, next = 
		(
			match inst with 		 
		  | BINOP op -> 
				let y::x::stack' = stack in
				let res = Value.of_int (Expr.eval_binop op (Value.to_int x) (Value.to_int y)) in
				(cstack, res :: stack', c), prog_tail

			| CONST z  -> (cstack, (Value.of_int z)::stack, c), prog_tail
			
			| STRING s -> (cstack, (Value.of_string s)::stack, c), prog_tail

			| LD x -> (cstack, (State.eval st x) :: stack, c), prog_tail
			
			| ST x -> 
				let num = List.hd stack in 
				(cstack, List.tl stack, (State.update x num st, i, o)), prog_tail

			| STA (x, n) -> 
				let value::taken, rest = split (n + 1) stack in
				(cstack, rest, (Stmt.update st x value taken, i, o)), prog_tail
			
			| SEXP (s, vals) -> 
				let exprs, rest = split vals stack in 
				(cstack, (Value.sexp s (List.rev exprs)) :: rest, c), prog_tail
								
			| LABEL s -> conf, prog_tail
			
			| JMP label -> conf, (env#labeled label)
			
			| CJMP (cond, label) -> 
        (cstack, List.tl stack, c),
        (
          if (check_cond_jmp cond (List.hd stack)) 
          then (env#labeled label) 
          else prog_tail
				)
				
			| CALL (fname, n, p) -> 
        if env#is_label fname
        then ((prog_tail, st)::cstack, stack, c), (env#labeled fname) 
        else (env#builtin conf fname n p), prog_tail

		  | BEGIN (_, params, xs) ->
				let new_st = State.enter st (params @ xs) in
				let args, rest = split (List.length params) stack in
				let evf = fun ast p v -> State.update p v ast in
				let st' = List.fold_left2 evf new_st params (List.rev args) in
				(cstack, rest, (st', i, o)), prog_tail

			| END | RET _ -> 
				(
					match cstack with
					| (prog_tail, st')::cstack' -> (cstack', stack, (State.leave st st', i, o)), prog_tail
					| [] -> conf, []
				)

			| DROP -> (cstack, List.tl stack, c), prog_tail
			
			| DUP -> let hd::_ = stack in (cstack, hd::stack, c), prog_tail
			
			| SWAP -> let x::y::rest = stack in (cstack, y::x::rest, c), prog_tail
			
			| TAG s -> 
				let sexp::tl = stack in 
				let res = if s = Value.tag_of sexp then 1 else 0 in 
				(cstack, (Value.of_int res)::tl, c), prog_tail
			
		  | ENTER es -> 
				let vals, rest = split (List.length es) stack in
				let evf = fun ast e var -> State.bind var e ast in
				let st' = List.fold_left2 evf State.undefined vals es in 
				(cstack, rest, (State.push st st' es, i, o)), prog_tail
						
			| LEAVE -> (cstack, stack, (State.drop st, i, o)), prog_tail
		) in
	  eval env cfg next;;

(* Top-level evaluation
     val run : prg -> int list -> int list
   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
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
let compile (defs, p) = 
  let label s = "L" ^ s in
	
	let rec compile_call f args p =
    let compiled_args = List.concat @@ List.map compile_expr args in
    compiled_args @ [CALL (f, List.length args, p)]
    and pattern p lfalse =
    (
			let rec compile_pattern patt =
      (
				match patt with
					Stmt.Pattern.Wildcard -> [DROP]
				| Stmt.Pattern.Ident x -> [DROP]
				| Stmt.Pattern.Sexp (tag, ps) ->
					let evf = 
						(
							fun (acc, pos) patt -> 
							(acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ (compile_pattern patt)), pos + 1
						) 
					in
					let res, _ = (List.fold_left evf ([], 0) ps) in
					[DUP; TAG tag; CJMP ("z", lfalse)] @ res
			) in 
			compile_pattern p
		)
	
	and compile_bindings p =
    let rec bind cp = 
      (match cp with
        Stmt.Pattern.Wildcard -> 	[DROP]
      | Stmt.Pattern.Ident x -> 	[SWAP]
			| Stmt.Pattern.Sexp (_, xs) ->
				let evf = 
					(
						fun (acc, pos) curp -> 
						(acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ bind curp, pos + 1)
					) 
				in
        let res, _ = List.fold_left evf ([], 0) xs in res @ [DROP]) in
    bind p @ [ENTER (Stmt.Pattern.vars p)]
	
	and compile_expr e =
		match e with
		| Expr.Var x -> [LD x]
		| Expr.Const n -> [CONST n]
		| Expr.Binop (op, x, y) -> compile_expr x @ compile_expr y @ [BINOP op]
		| Expr.String s -> [STRING s]
		| Expr.Sexp (s, exprs) ->
			let evf = (fun acc index -> acc @ (compile_expr index)) in
			let args = List.fold_left evf [] exprs in args @ [SEXP (s, List.length exprs)]
		| Expr.Array arr -> 
			List.flatten (List.map compile_expr arr) @ [CALL (".array", List.length arr, false)]
		| Expr.Length t -> compile_expr t @ [CALL (".length", 1, false)]
		| Expr.Elem (arr, i) -> compile_expr arr @ compile_expr i @ [CALL (".elem", 2, false)]
		| Expr.Call (f, args) -> compile_call (label f) args false in
		
  let rec compile_stmt l env stmt =
    match stmt with
		| Stmt.Assign (x, [], e) -> env, false, compile_expr e @ [ST x]
		
		| Stmt.Assign (x, is, e) -> 
			let evf = (fun acc index -> acc @ (compile_expr index)) in
			let indexes = List.fold_left evf [] is in 
			env, false, (List.rev indexes @ compile_expr e @ [STA (x, List.length is)])
			
    | Stmt.Seq (left_st, right_st) ->
      let env, _, left = compile_stmt l env left_st in
      let env, _, right = compile_stmt l env right_st in
			env, false, left @ right
			
		| Stmt.Skip -> env, false, []
		
    | Stmt.If (cond, then_body, else_body) ->
      let else_label, env = env#new_label in
      let end_label, env = env#new_label in
      let env, _, then_case = compile_stmt l env then_body in
      let env, _, else_case = compile_stmt l env else_body in
			env, false, 
			(compile_expr cond) @ 
			[CJMP ("z", else_label)] @ 
			then_case @ 
			[JMP end_label] @ 
			[LABEL else_label] @ 
			else_case @ 
			[LABEL end_label]
			
    | Stmt.While (cond, while_body) ->
      let end_label, env = env#new_label in
      let loop_label, env = env#new_label in
      let env, _, compiled_body = compile_stmt l env while_body in
			env, false, 
			[JMP end_label] @ 
			[LABEL loop_label] @ 
			compiled_body @ 
			[LABEL end_label] @ 
			compile_expr cond @ 
			[CJMP ("nz", loop_label)]
			
    | Stmt.Repeat (cond, repeat_body) ->
      let loop_label, env = env#new_label in
      let env, _, compiled_body = compile_stmt l env repeat_body in
			env, false, 
			[LABEL loop_label] @ 
			compiled_body @ 
			compile_expr cond @ 
			[CJMP ("z", loop_label)]
			
		| Stmt.Return e -> 
			(
				match e with
				| Some e -> env, false, compile_expr e @ [RET true]
				| None -> env, false, [RET false]
			)

    | Stmt.Call (name, args) -> 
			env, false, 
			List.concat (List.map compile_expr args) @ 
			[CALL ("L" ^ name, List.length args, true)]
			
    | Stmt.Case (e, patterns) ->
      let rec compile_patterns ps env lbl is_first lend = 
      (
				match ps with
        [] -> env, []
        | (p, act)::tl -> 
          let env, _, compiled_body = compile_stmt l env act in 
          let lfalse, env = env#new_label
          and start = if is_first then [] else [LABEL lbl] in
          let env, code = compile_patterns tl env lfalse false lend in
					env, start @ 
					(pattern p lfalse) @ 
					compile_bindings p @ 
					compiled_body @ 
					[LEAVE; JMP lend] @ code
			) 
			in
      let lend, env = env#new_label in
      let env, compiled_patterns = compile_patterns patterns env "" true lend in
			env, false, 
			(compile_expr e) @ 
			compiled_patterns @ 
			[LABEL lend]
			
		| Stmt.Leave -> env, false, [LEAVE] in
		
  let compile_fun_def env (name, (args, locals, stmt)) =
    let lend, env       = env#new_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
		(
			if flag 
			then [LABEL lend] 
			else []
		) 
		@	[END]
		
  in
  let env =
    object
      val counter = 0
      method new_label = (label @@ string_of_int counter), {< counter = counter + 1 >}
    end
  in
	let env, compiled_functions =
		let evf = 
			(
				fun (env, code) (name, others) -> 
				let env, code' = compile_fun_def env (label name, others) in 
				env, code'::code
			) 
		in
    List.fold_left evf (env, []) defs
  in
  let lend, env = env#new_label in
  let _, flag, code = compile_stmt lend env p in
	(
		if flag 
		then code @ [LABEL lend] 
		else code
	) 
	@ [END] @ (List.concat compiled_functions) 