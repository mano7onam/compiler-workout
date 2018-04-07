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
          val eval : env -> config -> t -> int * config
       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method
           method definition : env -> string -> int list -> config -> config
       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
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

    let rec eval env ((st, i, o, r) as conf) expr = 
    	match expr with
		| Const c -> (st, i, o, Some c)
		| Var v -> let res = State.eval st v in	(st, i, o, Some res)
		| Binop (op, a, b) ->
		  let (st', i', o', Some a') as conf' = eval env conf a in
		  let (st', i', o', Some b') = eval env conf' b in
		  let res = eval_binop op a' b' in 
		  (st', i', o', Some res)
		| Call (fun_name, args) ->
			let rec evalArgs env conf args =
				match args with
		 		| expr::args' ->
		 			let (st', i', o', Some eval_arg) as conf' = eval env conf expr in
		 			let eval_args', conf' = evalArgs env conf' args' in 
					eval_arg::eval_args', conf'
		 		| [] -> [], conf  
		 	in
		 	let eval_args, conf' = evalArgs env conf args in
		 	env#definition env fun_name eval_args conf'
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
          fname:IDENT "(" args:!(Util.list0)[parse] ")" {Call (fname, args)}
        | v:IDENT   {Var v} 
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
    (* loop with a post-condition       *) | Repeat of Expr.t * t
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator
         val eval : env -> config -> t -> config
       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env conf k stmt =
    	let romb stmt k =
    		if k = Skip then stmt
    		else Seq (stmt, k) in
      
      match stmt, conf with
    	| Assign (x, e), (st, i, o, r) -> 
    		let (st', i', o', Some value) = Expr.eval env conf e in
        eval env (State.update x value st', i', o', r) Skip k
        
    	| Read x, (st, z::i, o, r) ->
        eval env (State.update x z st, i, o, r) Skip k
        
    	| Write e, (st, i, o, r) ->
    		let (st', i', o', Some value) = Expr.eval env conf e in
        eval env (st', i', o' @ [value], r) Skip k
        
    	| Seq (a, b), conf ->
        eval env conf (romb b k) a
        
    	| Skip, conf -> 
    		if k = Skip then conf
        else eval env conf Skip k
        
    	| If (cond, the, els), (st, i, o, r) ->
    		let (st', i', o', Some value) as conf' = Expr.eval env conf cond in
    		let if_answer value = if value == 0 then els else the in
        eval env conf' k (if_answer value)
        
    	| While (cond, body), conf ->
    		let (st', i', o', Some res_cond) as conf' = Expr.eval env conf cond in
        if res_cond == 0 
        then eval env conf' Skip k
        else eval env conf' (romb stmt k) body
        
    	| Repeat (cond, body), conf ->
        eval env conf (romb ( While(Expr.Binop("==", cond, Expr.Const 0), body)) k) body
        
    	| Call (fun_name, args), (st, i, o, r) ->
        let rec eval_args env conf = function
          | expr::args' ->
            let (st', i', o', Some evaled_arg) = Expr.eval env conf expr in
            let evaled_args', conf' = eval_args env (st', i', o', Some evaled_arg) args' in 
            evaled_arg::evaled_args', conf'
          | [] -> [], conf  
        in
        let evaled_args, conf' = eval_args env conf args in
        let conf'' = env#definition env fun_name evaled_args conf' in
        eval env conf'' Skip k
       
      | Return expr, (st, i, o, r) -> 
      (
        match expr with
        | None -> (st, i, o, None)
        | Some expr -> Expr.eval env conf expr
      )

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
        | %"repeat" act:parse %"until" cond: !(Expr.parse)    { Repeat (cond, act) }
        | %"for" init:parse "," cond: !(Expr.parse)
          "," inc:parse %"do" act:parse %"od"                 { Seq (init, While (cond, Seq (act, inc))) }
        | %"return" expr:!(Expr.parse)?                       { Return expr}
        | f:IDENT "(" args:function_s ")"                     { Call (f, args) }
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
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
  let module M = Map.Make (String) 
  in let defs_map = List.fold_left (fun defs_map ((name, _) as def) -> M.add name def defs_map) M.empty defs 
  in let _, _, output, _ =
    Stmt.eval
    (
      object
        method definition env f args (st, i, o, r) =
        let xs, locs, s = snd @@ M.find f defs_map in
        let st' = List.fold_left 
          (fun st (x, a) -> State.update x a st) 
          (State.enter st (xs @ locs)) 
          (List.combine xs args) 
        in let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s 
        in (State.leave st'' st, i', o', r')
      end
    ) 
    (State.empty, i, [], None)
    Stmt.Skip
    body
  in output

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))