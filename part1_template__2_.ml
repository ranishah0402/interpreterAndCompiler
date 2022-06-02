(* util functions *)

let is_lower_case c =
  'a' <= c && c <= 'z'

let is_upper_case c =
  'A' <= c && c <= 'Z'

let is_alpha c =
  is_lower_case c || is_upper_case c

let is_digit c =
  '0' <= c && c <= '9'

let is_alphanum c =
  is_lower_case c ||
  is_upper_case c ||
  is_digit c

let is_blank c =
  String.contains " \012\n\r\t" c

let explode s =
  List.of_seq (String.to_seq s)

let implode ls =
  String.of_seq (List.to_seq ls)

let readlines (file : string) : string =
  let fp = open_in file in
  let rec loop () =
    match input_line fp with
    | s -> s ^ "\n" ^ (loop ())
    | exception End_of_file -> ""
  in
  let res = loop () in
  let () = close_in fp in
  res

(* end of util functions *)

(* parser combinators *)

type 'a parser = char list -> ('a * char list) option

let parse (p : 'a parser) (s : string) : ('a * char list) option =
  p (explode s)

let pure (x : 'a) : 'a parser =
  fun ls -> Some (x, ls)

let fail : 'a parser = fun ls -> None

let bind (p : 'a parser) (q : 'a -> 'b parser) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> q a ls
  | None -> None

let (>>=) = bind
let (let*) = bind

let read : char parser =
  fun ls ->
  match ls with
  | x :: ls -> Some (x, ls)
  | _ -> None

let satisfy (f : char -> bool) : char parser =
  fun ls ->
  match ls with
  | x :: ls ->
    if f x then Some (x, ls)
    else None
  | _ -> None
let satisfy2 (f : string -> bool) : string parser =
  fun ls ->
  match ls with
  | x :: x2 :: ls ->
    if f (implode (x::[x2])) then Some ((implode (x::[x2])), ls)
    else None
  | _ -> None

let char (c : char) : char parser =
  satisfy (fun x -> x = c)

let seq (p1 : 'a parser) (p2 : 'b parser) : 'b parser =
  fun ls ->
  match p1 ls with
  | Some (_, ls) -> p2 ls
  | None -> None

let (>>) = seq

let seq' (p1 : 'a parser) (p2 : 'b parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls) ->
    (match p2 ls with
     | Some (_, ls) -> Some (x, ls)
     | None -> None)
  | None -> None

let (<<) = seq'

let alt (p1 : 'a parser) (p2 : 'a parser) : 'a parser =
  fun ls ->
  match p1 ls with
  | Some (x, ls)  -> Some (x, ls)
  | None -> p2 ls

let (<|>) = alt

let map (p : 'a parser) (f : 'a -> 'b) : 'b parser =
  fun ls ->
  match p ls with
  | Some (a, ls) -> Some (f a, ls)
  | None -> None

let (>|=) = map

let (>|) = fun p c -> map p (fun _ -> c)

let rec many (p : 'a parser) : ('a list) parser =
  fun ls ->
  match p ls with
  | Some (x, ls) ->
    (match many p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> Some ([], ls)

let rec many1 (p : 'a parser) : ('a list) parser =
  fun ls ->
  match p ls with
  | Some (x, ls) ->
    (match many p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> None

let rec many' (p : unit -> 'a parser) : ('a list) parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) ->
    (match many' p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> Some ([], ls)

let rec many1' (p : unit -> 'a parser) : ('a list) parser =
  fun ls ->
  match p () ls with
  | Some (x, ls) ->
    (match many' p ls with
     | Some (xs, ls) -> Some (x :: xs, ls)
     | None -> Some (x :: [], ls))
  | None -> None

let whitespace : unit parser =
  fun ls ->
  match ls with
  | c :: ls ->
    if String.contains " \012\n\r\t" c
    then Some ((), ls)
    else None
  | _ -> None

let ws : unit parser =
  (many whitespace) >| ()

let ws1 : unit parser =
  (many1 whitespace) >| ()

let digit : char parser =
  satisfy is_digit

let natural : int parser =
  fun ls ->
  match many1 digit ls with
  | Some (xs, ls) ->
    Some (int_of_string (implode xs), ls)
  | _ -> None

let literal (s : string) : unit parser =
  fun ls ->
  let cs = explode s in
  let rec loop cs ls =
    match cs, ls with
    | [], _ -> Some ((), ls)
    | c :: cs, x :: xs ->
      if x = c
      then loop cs xs
      else None
    | _ -> None
  in loop cs ls

let keyword (s : string) : unit parser =
  (literal s) >> ws >| ()

(* end of parser combinators *)



(* start of my code*)
(* type defintions *)
type nameType = string 
type const = Nat of int | Name of string | UnitType | Closure of nameType * nameType * (command list) * env
and  env =  (const * const) list 
and  command = Push of const 
             | Add 
             | Sub 
             | Mul 
             | Div 
             | Trace 
             | IfElseEnd of (command list *command list)
             | Let 
             | Lookup
             | BeginEnd of command list
             | FunEnd of (nameType  * nameType * command list) (* will have to check const is name *)
             | Call

(* for IfElseEnd it would have (command list *command list) inside it *)
type prog = Prog of command list


let reserved = [
  "Push";
  "Add";
  "Sub";
  "Mul";
  "Div";
  "Trace";
  "Let";
  "If";
  "Else";
  "Fun";
  "End";
]

let is_initial ch : bool = 
  if ch = '_' || is_alpha ch then true else false 
let is_name ch : bool = 
  if ch = '_' || ch = '\'' || is_alphanum ch then true else false 
let is_unit str : bool = 
  match (parse (keyword "()")) str with
  | Some v ->  true
  | None -> false 

let nameStringParser : string parser = 
  let* xs1 = many1 (satisfy (fun c -> is_alpha c || c = '_')) in
  let* xs2 = 
    many (satisfy (fun c ->
        is_alphanum c ||
        (c = '_') ||
        (c = '\'')))
  in
  let s = (implode xs1) ^ (implode xs2) in
  if List.exists (fun x -> x = s) reserved
  then fail
  else pure s << ws
let name_parser () =
  let* n = nameStringParser in
  pure (Name n)

let constParser : const parser = 
  (natural >>= fun n -> pure (Nat n)) <|> 
  ((satisfy2 is_unit ) >> pure UnitType) <|>
  (name_parser () ) 





(* mini parsers for each type of command *)
let  addParser  = 
  keyword "Add" >>= fun c1 ->
  pure Add
let  subParser  = 
  keyword "Sub" >>= fun c1 ->
  pure Sub
let  mulParser  = 
  keyword "Mul" >>= fun c1 ->
  pure Mul
let  divParser  = 
  keyword "Div" >>= fun c1 ->
  pure Div 

let  pushParser  = 
  keyword "Push" >>= fun c1 ->
  ws>>= fun _ ->
  constParser >>= fun n -> 
  ws>>= fun _ ->
  (pure (Push n))  


let  traceParser  = 
  keyword "Trace" >>= fun c1 ->
  pure Trace

let theLetParser = 
  keyword "Let" >>= fun c1 ->
  pure Let
let lookupParser = 
  keyword "Lookup" >>= fun c1 ->
  pure Lookup
let callParser = 
  keyword "Call" >>= fun c1 ->
  pure Call

let rec comParser () =  
  pushParser <|> 
  addParser <|> 
  subParser <|>
  mulParser <|>
  divParser <|>
  traceParser <|>
  theLetParser <|>
  lookupParser <|>
  ifElseEndParser () <|>
  beginEndParser () <|>
  funEndParser () <|>
  callParser
and comsParser () = 
  many' comParser

(* i think that this is what the parser for ifelseend should do?*)
and  ifElseEndParser () = 
  keyword "If" >>= fun c1 ->
  ws >>= fun _ ->
  comsParser () >>= fun c2 ->
  ws >>= fun _ ->
  keyword "Else" >>= fun c3 -> 
  ws >>= fun _ ->
  comsParser () >>= fun c4 ->
  ws >>= fun _ ->
  keyword "End" >>= fun c5 -> 
  pure (IfElseEnd (c2, c4))

and beginEndParser () = 
  keyword "Begin" >>= fun c1 -> 
  ws >>= fun _ ->
  comsParser () >>= fun c2 ->
  ws >>= fun _ ->
  keyword "End" >>= fun c3 ->
  pure(BeginEnd c2)

and funEndParser () = 
  keyword "Fun" >>= fun c1 ->
  ws >>= fun _ ->
  nameStringParser  >>= fun c2 -> 
  ws >>= fun _ ->
  nameStringParser  >>= fun c3 ->
  ws >>= fun _ -> 
  comsParser () >>= fun c4 ->
  ws >>= fun _ -> 
  keyword "End" >>= fun c5 ->
  pure (FunEnd (c2, c3, c4))


(* this would programs?*)
let progParser = 
  comParser () >>= fun com -> 
  many ( 
    ws >>= fun _ -> 
    comParser () >>= fun com -> 
    pure com 
  ) >>= fun prog ->
  pure (com::prog)


let rec lookupChecker valX envLs = 
  match envLs with 
  | (Name nam, val1 ) ::t2 -> if nam = valX  then  Some val1 else lookupChecker valX t2
  | h::t -> lookupChecker valX t
  | [] -> None


let rec execute (comm_ls: command list) (stack: const list) (log: const list) (environ: env):  (const list *const list * env) option = 
  match ( comm_ls) with 
  | Add ::tail -> (match stack with 
      | x :: y ::t -> (match x, y with 
          |Nat x, Nat y ->  execute tail (Nat ( x+ y)::t) log environ
          |_ -> None)
      | _ -> None)
  | Sub :: tail -> (match stack with 
      | x :: y ::t -> (match x, y with 
          |Nat x, Nat y ->  execute tail (Nat ( y-x)::t) log environ
          |_ -> None)
      | _ -> None)
  | Mul :: tail -> (match stack with 
      | x :: y ::t -> (match x, y with 
          |Nat x, Nat y -> execute tail (Nat ( x* y)::t) log environ
          |_ -> None)
      | _ -> None)
  | Div :: tail -> (match stack with 
      | x :: y ::t -> (match x, y with 
          |Nat x, Nat y -> if x>0 then execute tail (Nat ( y/x)::t) log environ else (None)
          |_ -> None)
      | _ -> None)
  | Push x :: tail -> execute tail (x::stack ) log environ
  | Trace :: tail -> (match stack with 
      | Closure (n1, n2, cl1, env2 ) :: t2 -> execute tail (UnitType::t2) ((Name("<fun>"))::log) environ
      | h::t -> execute tail (UnitType::t) (h::log) environ
      |[] -> None)
  | IfElseEnd (cl1, cl2):: tail ->  (match (match stack with 
      |Nat x::tail -> if x>0 then execute cl1 (tail) log environ else execute cl2 (tail) log environ
      | _ -> None ) with 
    |Some (l1, l2, l3) -> (match l1 with 
        | h::t -> execute (tail) l1 l2 environ
        |_ -> None)
    |_->None)
  | Let::tail ->  (match stack with 
      |h1::h2::t -> execute tail (t) log ((h2, h1)::environ)
      |_ -> None) 
  | Lookup :: tail -> (match stack with 
      | Name x :: t ->  (match (lookupChecker x environ) with 
          |Some v -> execute tail (v::t) log environ 
          |None -> None )  (* Right now lookup only works for looking up elements at top of environment*)
      |_ -> None)
  | BeginEnd (cl) :: tail -> (match (execute cl [] log environ ) with 
      | Some (h::t, log2, environ2) -> execute tail (h::stack) log2 environ
      |_-> None)
  |FunEnd (fname, arg, cl2) :: tail -> execute tail stack  log ((Name fname, (Closure ( fname, arg, cl2, environ)))::environ )
  |Call :: tail -> (match stack with 
      |x::(Closure(fname, arg, commLs2, env2))::rest ->(match(execute commLs2 [] log ((Name fname, (Closure(fname, arg, commLs2, env2)))::(Name arg, x)::env2)) with 
          |Some (h::t, log2, environ2) -> execute tail (h::rest) log2 environ
          |Some _ -> execute tail stack log environ
          |None -> None)
      |_-> None ) (* this is definitely wrong LOL im j bored*)
  |[] -> Some (stack,log, environ)
(* still need to fix the call piece *)

let const_to_string (c: const) : string = 
  match c with 
  | Nat n -> string_of_int n
  | Name a -> a 
  | UnitType -> "()"
  | Closure (n1, n2, cl, en) -> n2

let const_list_to_string_list (clist: const list) : string list = 
  let rec aux cl accum = 
    match cl with 
    |h::t -> aux t ((const_to_string h)::accum)
    |[] -> accum 
  in aux clist []

(* Interprets a program written in the Part1 Stack Language.
 * Required by the autograder, do not change its type. *)
let interpreter (src : string) : (string * string list) =
  match parse progParser src with 
  | Some ( a, []) -> (match execute a [] [] [] with 
      | Some (h::t, log, environ) -> (const_to_string h, List.rev(const_list_to_string_list log))
      |Some _ -> ("", [])
      | None -> ("Error", []))
  |Some (a, ls) -> ("Error", [])
  | None -> ("Error", [])

let printStack (str: string) : string list = 
  match parse progParser str with 
  | Some ( a, []) -> (match execute a [] [] [] with 
      | Some (stack, log, environ) -> (List.rev(const_list_to_string_list stack))
      | None -> (["Error"]))
  |Some (a, ls) -> (["Error"])
  | None -> (["Error"])

let printEnvironment (str: string) : env  = 
  match parse progParser str with 
  | Some ( a, []) -> (match execute a [] [] [] with 
      | Some (stack, log, environ) -> (( environ))
      | None -> ([]))
  |Some (a, ls) -> ([])
  | None -> ([])

let testInterp  = interpreter "Begin
Push fibo
Fun fibo n
Begin
Push eq
Fun eq x
Fun _ y
Push x
Lookup
If
Begin
Push y
Lookup
If
Begin
Push eq
Lookup
Push x
Lookup
Push 1
Sub
Call
Push y
Lookup
Push 1
Sub
Call
End
Else
Begin
Push 0
End
End
End
Else
Begin
Push y
Lookup
If
Begin
Push 0
End
Else
Begin
Push 1
End
End
End
End
End
Push _
Lookup
End
Push eq
Lookup
Let
Begin
Push kfibo
Fun kfibo n
Fun _ k
Push n
Lookup
If
Begin
Push eq
Lookup
Push n
Lookup
Call
Push 1
Call
If
Begin
Push k
Lookup
Push 1
Call
End
Else
Begin
Push kfibo
Lookup
Push n
Lookup
Push 1
Sub
Call
Fun _ res1
Push kfibo
Lookup
Push n
Lookup
Push 2
Sub
Call
Fun _ res2
Push k
Lookup
Push res1
Lookup
Push res2
Lookup
Add
Call
End
Push _
Lookup
Call
End
Push _
Lookup
Call
End
End
End
Else
Begin
Push k
Lookup
Push 0
Call
End
End
End
Push _
Lookup
End
Push kfibo
Lookup
Let
Push kfibo
Lookup
Push n
Lookup
Call
Fun _ x
Push x
Lookup
End
Push _
Lookup
Call
End
End
End
Push fibo
Lookup
Let
Push fibo
Lookup
Push 10
Call
End
"

let testEnv = printEnvironment "Begin
Push fibo
Fun fibo n
Begin
Push eq
Fun eq x
Fun _ y
Push x
Lookup
If
Begin
Push y
Lookup
If
Begin
Push eq
Lookup
Push x
Lookup
Push 1
Sub
Call
Push y
Lookup
Push 1
Sub
Call
End
Else
Begin
Push 0
End
End
End
Else
Begin
Push y
Lookup
If
Begin
Push 0
End
Else
Begin
Push 1
End
End
End
End
End
Push _
Lookup
End
Push eq
Lookup
Let
Begin
Push kfibo
Fun kfibo n
Fun _ k
Push n
Lookup
If
Begin
Push eq
Lookup
Push n
Lookup
Call
Push 1
Call
If
Begin
Push k
Lookup
Push 1
Call
End
Else
Begin
Push kfibo
Lookup
Push n
Lookup
Push 1
Sub
Call
Fun _ res1
Push kfibo
Lookup
Push n
Lookup
Push 2
Sub
Call
Fun _ res2
Push k
Lookup
Push res1
Lookup
Push res2
Lookup
Add
Call
End
Push _
Lookup
Call
End
Push _
Lookup
Call
End
End
End
Else
Begin
Push k
Lookup
Push 0
Call
End
End
End
Push _
Lookup
End
Push kfibo
Lookup
Let
Push kfibo
Lookup
Push n
Lookup
Call
Fun _ x
Push x
Lookup
End
Push _
Lookup
Call
End
End
End
Push fibo
Lookup
Let
Push fibo
Lookup
Push 10
Call
End
"

let testStack = printStack "Begin
Push fibo
Fun fibo n
Begin
Push eq
Fun eq x
Fun _ y
Push x
Lookup
If
Begin
Push y
Lookup
If
Begin
Push eq
Lookup
Push x
Lookup
Push 1
Sub
Call
Push y
Lookup
Push 1
Sub
Call
End
Else
Begin
Push 0
End
End
End
Else
Begin
Push y
Lookup
If
Begin
Push 0
End
Else
Begin
Push 1
End
End
End
End
End
Push _
Lookup
End
Push eq
Lookup
Let
Begin
Push kfibo
Fun kfibo n
Fun _ k
Push n
Lookup
If
Begin
Push eq
Lookup
Push n
Lookup
Call
Push 1
Call
If
Begin
Push k
Lookup
Push 1
Call
End
Else
Begin
Push kfibo
Lookup
Push n
Lookup
Push 1
Sub
Call
Fun _ res1
Push kfibo
Lookup
Push n
Lookup
Push 2
Sub
Call
Fun _ res2
Push k
Lookup
Push res1
Lookup
Push res2
Lookup
Add
Call
End
Push _
Lookup
Call
End
Push _
Lookup
Call
End
End
End
Else
Begin
Push k
Lookup
Push 0
Call
End
End
End
Push _
Lookup
End
Push kfibo
Lookup
Let
Push kfibo
Lookup
Push n
Lookup
Call
Fun _ x
Push x
Lookup
End
Push _
Lookup
Call
End
End
End
Push fibo
Lookup
Let
Push fibo
Lookup
Push 10
Call
End
"
