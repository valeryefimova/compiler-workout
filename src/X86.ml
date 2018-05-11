(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string
                                                                            
(* Instruction printer *)
let show instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s

(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)
let suffix = function
  | "<"  -> "l"
  | "<=" -> "le"
  | "==" -> "e"
  | "!=" -> "ne"
  | ">=" -> "ge"
  | ">"  -> "g"
  | _    -> failwith "unknown operator"

let in_mem = function
  | S _ | M _ -> true
  | _   -> false

let mov (a, b) = if in_mem a && in_mem b then [Mov (a, eax); Mov (eax, b)] else [Mov (a, b)]

let binop (op, a, b) = if in_mem a && in_mem b then [Mov (b, eax); Binop (op, a, eax); Mov (eax, b)] else [Binop (op, a, b)]

let call env f n p =
  let f =
    match f.[0] with
    | '.' -> "B" ^ String.sub f 1 (String.length f - 1)
    | _ -> f
  in
  let pushr, popr =
    List.split @@ List.map (fun r -> (Push r, Pop r)) (env#live_registers n)
  in
  let env, code =
    if n = 0
    then env, pushr @ [Call f] @ (List.rev popr)
    else
      let rec push_args env acc = function
      | 0 -> env, acc
      | n -> let x, env = env#pop in
             push_args env ((Push x)::acc) (n-1)
      in
      let env, pushs = push_args env [] n in
      let pushs      =
        match f with
        | "Barray" -> List.rev @@ (Push (L n))     :: pushs
        | "Bsta"   ->
           let x::v::is = List.rev pushs in
           is @ [x; v] @ [Push (L (n-2))]
        | _  -> List.rev pushs
      in
      env, pushr @ pushs @ [Call f; Binop ("+", L (n*4), esp)] @ (List.rev popr)
  in
  (if p then env, code else let y, env = env#allocate in env, code @ [Mov (eax, y)])

let char_code = function
| '_' -> 53
| c -> if (c > 'Z') then Char.code c - 70 else Char.code c - 64

let save_tag tag =
  let len = String.length tag in
  let substr = String.sub tag 0 (min len 5) in
  let rec str_to_int str acc all k =
    if (k >= all) then acc
    else str_to_int tag ((acc lsl 6) lor (char_code tag.[k])) all (k + 1)
  in
  str_to_int substr 0 len 0

let rec compile' env = function
  | CONST n  -> let s, env' = env#allocate in (env', [Mov (L n, s)])
  | LD x     -> let s, env' = (env#global x)#allocate in (env', mov (env'#loc x, s))
  | ST x     -> let s, env' = (env#global x)#pop in (env', mov (s, env'#loc x))
  | BINOP op ->
    let x, y, env = env#pop2 in
    let s, env = env#allocate in
    (match op with
     | "+" | "-" | "*" -> env, binop (op, x, y) @ mov (y, s)
     | "&&" | "!!" ->
       env, [Binop ("^", eax, eax); Binop ("^", edx, edx);
             Binop ("cmp", L 0, x); Set ("nz", "%al");
             Binop ("cmp", L 0, y); Set ("nz", "%dl");
             Binop (op, eax, edx); Mov (edx, s)]
     | "/" -> env, [Mov (y, eax); Cltd; IDiv x; Mov (eax, s)]
     | "%" -> env, [Mov (y, eax); Cltd; IDiv x; Mov (edx, s)]
     | "<" | "<=" | ">" | ">=" | "==" | "!=" ->
       env, binop ("cmp", x, y) @ [Mov (L 0, eax); Set ((suffix op), "%al"); Mov(eax, s)])
  | LABEL s     -> env, [Label s]
  | JMP   l     -> env, [Jmp l]
  | CJMP (s, l) ->
    let x, env = env#pop in
    env, [Binop ("cmp", L 0, x); CJmp  (s, l)]
  | BEGIN (f, a, l) ->
    let env = env#enter f a l in
    env, [Push ebp; Mov (esp, ebp); Binop ("-", M ("$" ^ env#lsize), esp)]
  | END ->
    env, [Label env#epilogue;
          Mov (ebp, esp);
          Pop ebp;
          Ret;
          Meta (Printf.sprintf "\t.set\t%s, \t%d" env#lsize (env#allocated * word_size))]
  | RET b ->
    if b
    then let x, env = env#pop in env, [Mov (x, eax); Jmp env#epilogue]
    else env, [Jmp env#epilogue]
  | CALL (f, n, p) -> call env f n p
  | STA (x, n) ->
    let s, env = (env#global x)#allocate in
    let env, code = call env ".sta" (n + 2) true in
    env, mov (env#loc x, s) @ code
  | STRING s ->
    let s, env = env#string s in
    let l, env = env#allocate in
    let env, call = call env ".string" 1 false in
    env, (Mov (M ("$" ^ s), l) :: call)
  | SEXP (t, n) ->
    let env, code = call env ".sexp" (n + 1) true in
    env, [Push (L (save_tag t))] @ code
  | _ -> env, []

let rec compile env = function
| instr :: scode' ->
  let env',  code'  = compile' env  instr  in
  let env'', code'' = compile  env' scode' in
  env'', code' @ code''
| [] -> env, []

(* A set of strings *)           
module S = Set.Make (String)

(* A map indexed by strings *)
module M = Map.Make (String)

let init n f =
  let rec init' i n f =
    if i >= n then []
    else (f i) :: (init' (i + 1) n f)
  in init' 0 n f

(* Environment implementation *)
let make_assoc l = List.combine l (init (List.length l) (fun x -> x))
                     
class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stringm     = M.empty (* a string map                      *)
    val scount      = 0       (* string count                      *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
                        
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (List.assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
	let rec allocate' = function
	| []                            -> ebx     , 0
	| (S n)::_                      -> S (n+1) , n+2
	| (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
        | (M _)::s                      -> allocate' s
	| _                             -> S 0     , 1
	in
	allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = let x::stack' = stack in x, {< stack = stack' >}

    (* pops two operands from the symbolic stack *)
    method pop2 = let x::y::stack' = stack in x, y, {< stack = stack' >}

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* registers a string constant *)
    method string x =
      try M.find x stringm, self
      with Not_found ->
        let y = Printf.sprintf "string_%d" scount in
        let m = M.add x y stringm in
        y, {< scount = scount + 1; stringm = m>}
                       
    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets all string definitions *)      
    method strings = M.bindings stringm

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      {< stack_slots = List.length l; stack = []; locals = make_assoc l; args = make_assoc a; fname = f >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers depth =
      let rec inner d acc = function
      | []             -> acc
      | (R _ as r)::tl -> inner (d+1) (if d >= depth then (r::acc) else acc) tl
      | _::tl          -> inner (d+1) acc tl
      in
      inner 0 [] stack
       
  end
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const 0))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s      -> Meta (Printf.sprintf "%s:\t.int\t0"         s  )) env#globals) @
                               (List.map (fun (s, v) -> Meta (Printf.sprintf "%s:\t.string\t\"%s\"" v s)) env#strings) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ show i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)
 
