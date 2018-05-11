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
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (label f, List.length args, p)]
  and pattern lfalse _ = failwith "Not implemented"
  and bindings p = failwith "Not implemented"
  and expr e = failwith "Not implemented" in
  let rec compile_stmt l env stmt =  failwith "Not implemented" in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code) 

