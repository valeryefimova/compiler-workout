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
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let check_jmp s e =
    match s with
    | "z"  -> e = 0
    | "nz" -> e != 0

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
  | [] -> conf
  | insn :: prg' ->
  (match insn with
    | BINOP op    -> let y::x::stack' = stack in
      eval env (cstack, (Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y)))::stack', c) prg'
    | CONST i     -> eval env (cstack, (Value.of_int i)::stack, c) prg'
    | STRING s    -> eval env (cstack, (Value.of_string s)::stack, c) prg'
    | LD x        -> eval env (cstack, (State.eval st x ) :: stack, c) prg'
    | ST x        -> let z::stack'    = stack in eval env (cstack, stack', (State.update x z st, i, o)) prg'
    | STA (x, n)  -> let v::is, stack' = split (n + 1) stack in
                     eval env (cstack, stack', (Language.Stmt.update st x v (List.rev is), i , o)) prg'
    | LABEL l     -> eval env conf prg'
    | JMP l       -> eval env conf (env#labeled l)
    | CJMP (s, l) ->
      let z::stack' = stack in
      if (check_jmp s (Value.to_int z)) then eval env (cstack, stack', c) (env#labeled l) else eval env (cstack, stack', c) prg'
    | CALL (f, n, p) ->
      if env#is_label f
      then eval env ((prg', st)::cstack, stack, c) (env#labeled f)
      else eval env (env#builtin conf f n p) prg'
    | BEGIN (_, a, l) ->
      let (st', stack') = List.fold_right (fun a (st, x::stack') -> (
        State.update a x st, stack')) a (State.enter st (a @ l), stack) in
      eval env (cstack, stack', (st', i, o)) prg'
    | END | RET _ ->
      (match cstack with
      | [] -> conf
      | (p, st')::cstack' -> eval env (cstack', stack, (State.leave st st', i, o)) p
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

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

class env =
    object(self)
        val cnt = 0
        method next_label = "l" ^ string_of_int cnt, {<cnt = cnt + 1>}
    end

let rec compile' env =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.String s         -> [STRING s]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (f, args)   -> List.concat (List.map expr args) @ [CALL (f, List.length args, false)]
  | Expr.Array arr        -> List.concat (List.map expr arr) @ [CALL ("$array", List.length arr, false)]
  | Expr.Elem (a, i)      -> expr a @ expr i @ [CALL ("$elem", 2, false)]
  | Expr.Length e         -> expr e @ [CALL ("$length", 1, false)]
  in
  function
  | Stmt.Seq (s1, s2)  ->
        let env, cfg = compile' env s1 in
        let env, cfg' = compile' env s2 in
        env, cfg @ cfg'
  | Stmt.Assign (x, [], e) -> env, expr e @ [ST x]
  | Stmt.Assign (x, is, e) -> env, List.concat (List.map expr (is @ [e])) @ [STA (x, List.length is)]
  | Stmt.Skip          -> env, []
  | Stmt.If (e, s1, s2)->
        let lelse, env = env#next_label in
        let lfi, env = env#next_label in
        let env, compiled_then = compile' env s1 in
        let env, compiled_else = compile' env s2 in
        env, (expr e @ [CJMP ("z", lelse)] @ compiled_then @ [JMP lfi] @ [LABEL lelse] @ compiled_else @ [LABEL lfi])
  | Stmt.While (e, s)  ->
        let lch, env = env#next_label in
        let llp, env = env#next_label in
        let env, compiled_lp = compile' env s in
        env, ([JMP lch] @ [LABEL llp] @ compiled_lp @ [LABEL lch] @ expr e @ [CJMP ("nz", llp)])
  | Stmt.Repeat (s, e) ->
        let llp, env = env#next_label in
        let env, compiled_lp = compile' env s in
        env, ([LABEL llp] @ compiled_lp @ expr e @ [CJMP ("z", llp)])
  | Stmt.Call (f, args) ->
        let comp_args = List.concat (List.map expr args) in
        env, comp_args @ [CALL (f, List.length args, true)]
  | Stmt.Return e -> env, (match e with None -> [RET false] | Some e -> expr e @ [RET true])

let compile_def env (f, (args, locals, body)) =
    let env, res = compile' env body in
    [LABEL f; BEGIN (f, args, locals)] @ res @ [END]

let compile (defs, p) =
    let env', comp_prg = compile' (new env) p in
	comp_prg @ [END] @ List.concat (List.map (compile_def env') defs)
