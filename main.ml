(*
 * Programming Languages
 * Programming Assignment 5
 * Anish Tondwalkar
 * Theo Gutman-Solo
 *)


open Printf
open List
open Int32

let reverse2 (a,b) = (b,a)
let reverse3 (a,b,c) = (c,b,a)
let reverse4 (a,b,c,d) = (b,c,d,a)
let reverse5 (a,b,c,d,e) = (e,d,c,b,a)

(* Cool objects are stored as references to a data structure that holds the
 * type string and all the attributes of that object *)
type coolie =
        | Object of string * (string * int) list
        | Int of int32
        | String of string
        | Bool of bool
        | Void

type cool = coolie ref


(* This is our data structure to hold the annotated AST *)

type feature =
  | Attribute of attribute
  | Method of cool_method
and attribute =
  | AttrNoInit of identifier * cool_type
  | AttrInit of identifier * cool_type * expr
and cool_method = CoolMethod of identifier * (identifier * cool_type) list * cool_type * expr
and identifier = IDENT of int * string
and cool_type = CoolType of int * string
and cmpOp = Le | Lt | Eq
and constant = INT of int32 | STRING of string | ID of identifier | T | F
and unOp  = Not | Neg
and anExpr =
  | AssignmentEx of identifier * expr
  | DispatchEx of (expr option) * (cool_type option) * identifier * (expr list)
  | ConstantEx of constant
  | IfEx of expr * expr * expr
  | LoopEx of expr * expr
  | BlockEx of expr list
  | NewTypeEx of cool_type
  | IsVdEx of expr
  | BinOpEx of (int32 -> int32 -> int32) * expr * expr
  | CmpOpEx of cmpOp * expr * expr
  | UnOpEx of unOp * expr
  | LetEx of (identifier * cool_type * expr option) list * expr
  | CaseEx of expr * (identifier * cool_type * expr) list
  | Internal of string 
and expr =
  | EXPR of int * anExpr
  | TypedExpr of int * string * anExpr

type cool_Class = CLASS of cool_type * cool_type option * feature list
type parentMap = (string * string) list
type methodImp = MethodImp of string * string list * string * expr
type classImp = string * methodImp list

type mapClass = string * (attr list)
and classMap = mapClass list
and attr =
  | Attr of string * string * expr
  | AttrNI of string * string


(* some utility functions *)

(* splits a list in two at position n *)
let rec split n l = match l with
  | [] -> ([],[])
  | (h::t) -> if n == 0 then [],l
              else let (acc,ans) = split (n-1) t in  h::acc,ans;;


(*keeps track of how tall the stack is*)
let stacksize = ref 0;;

(*new locations for the store*)
let theloc = ref (-1);;
let newloc unit = theloc := !theloc +1; !theloc;;

(*analgous to the haskell stdlib function*)
let catMaybes : 'c. 'c option list -> 'c list = fun l -> List.rev (
        List.fold_left (fun acc -> (function Some x -> x::acc | None -> acc)) [] l
)

(*default types*)
let default t = match t with
        | "Int" -> ref (Int 0l)
        | "String" -> ref (String "")
        | "Bool" -> ref (Bool false)
        | _ -> ref Void

(* These are global for us to use as we need inside functions
 * ancillary to gen_expr *)

let classmap = ref [];;
let parentmap = ref [];;
let implementation = ref [];;

(* Least Common Ancestor *)
let lca xs ys = let rec drop n l = match (n,l) with
                        | 0,_ | _,[] -> []
                        | n,(x::xs) -> drop (n-1) xs in
                let rec walk xxs yys = match (xxs,yys) with
                       | (x::xs , y::ys) -> if x=y then xxs else walk xs ys
                       | _ -> ["Object"] in
                let i = length xs in
                let j = length ys in
                let k = min i j in
                hd (walk (drop (i-k) xs) (drop (j-k) ys))
let rec path a = a :: try path (assoc a !parentmap) with Not_found -> []
let lub a b = lca (path a) (path b)
(* Conformance relations *)
let rec leq a b = try
        let c = assoc a !parentmap in
        if a=b or b=c then true else leq c b
with Not_found -> false
        
(* Closest ancestor for use with Case Exprs *)
let closestancestor = fun t ts -> let wins = (filter (fun x -> leq t x) ts) in
                                  let hits = length wins in
                                  if hits = 0 then (failwith "ERROR") else 
                                          let lens = map length (map path wins) in
                                          snd (List.fold_left max (hd (combine lens wins)) (combine lens wins));;

(* evaluates all the exprs, threading the store and listing the results *)
let rec vals so env (vs,s) l = match l with
  | [] -> (vs,s)
  | e::es -> let (v,s1) = gen_expr so env s e in vals so env (v::vs,s1) es
(* gen_expr actually excecutes the code. This is pretty much directly transcribed from the OpSem *)
and gen_expr : cool -> (string * int) list -> (int * cool) list -> expr -> cool * (int * cool) list = fun so env store expr -> match expr with
        | TypedExpr (i,_,e) -> gen_expr so env store (EXPR (i,e))
        | EXPR (_,AssignmentEx (IDENT (_,id), e1)) ->
                        let (v1,s2) = gen_expr so env store e1 in
                        let l1 = assoc id env in
                        let s3 = (l1,v1)::s2 in
                          (v1,s3)
        | EXPR (i,ConstantEx (ID (IDENT (_,id)))) -> begin match id with "self" -> (so,store) | _ -> 
                        let l = assoc id env in
                        let v = assoc l store in
                          (v,store)
                        end
        | EXPR (_,ConstantEx (INT i)) -> (ref (Int i),store)
        | EXPR (_,ConstantEx (STRING s)) -> (ref (String s),store)
        | EXPR (_,ConstantEx T) -> (ref (Bool true),store)
        | EXPR (_,ConstantEx F) -> (ref (Bool false),store)
        | EXPR (i,NewTypeEx (CoolType (_,t))) ->
                        let t0 = (match t with
                          | "SELF_TYPE" -> (match !so with
                                           | (Object (s,_)) -> s
                                           | (Int _) -> "Int"
                                           | (String _) -> "String"
                                           | (Bool _) -> "Bool"
                                           | Void -> failwith "new Void? WTF?"
                                         )
                          | _ -> t
                          ) in
                        let aitiei = assoc t0 !classmap in
                        let li = map newloc aitiei in
                        let attrs = map (function | Attr (s,t,e) -> s | AttrNI (s,t) -> s) in
                        let types = map (function | Attr (s,t,e) -> t | AttrNI (s,t) -> t) in
                        let exprs = catMaybes (map (function | Attr (s,t,e) -> Some (s,e) | AttrNI (_,_) -> None) aitiei) in
                        let env2 = combine (attrs aitiei) li in
                        let v1 = ref (Object (t0,env2)) in
                        let di = map default (types aitiei) in
                        let ass (i,e) = EXPR (0,AssignmentEx (IDENT (0,i),e)) in
                        let s2 = (combine li di)@store in
                        let (v2,s3) = gen_expr v1 env2 s2 (EXPR (i,BlockEx (map ass exprs))) in
                          (v1,s3)
        | EXPR (i,DispatchEx (None,None,IDENT (_,f),l)) ->
                        stacksize := 1+ !stacksize;
                        if !stacksize = 1000 then (print_string (String.concat "" ["ERROR: " ; (string_of_int i) ; ": stackoverflow"]) ; exit 1;) else
                        let (vi,sn1) = vals so env ([],store) l in
                        (match !so with Object (x,aili) ->
                                let xi,en1 = assoc (x,f) !implementation in
                                let lxi = map newloc xi in
                                let ans = gen_expr so ((combine xi lxi)@aili) ((combine lxi vi)@sn1) en1 in
                                        stacksize := !stacksize -1; ans
                                | Int _ -> let xi,en1 = assoc ("Int",f) !implementation in
                                           let lxi = map newloc xi in
                                           let ans = gen_expr so (combine xi lxi) ((combine lxi vi)@sn1) en1 in
                                                stacksize := !stacksize -1; ans
                                | Bool _ -> let xi,en1 = assoc ("Bool",f) !implementation in
                                            let lxi = map newloc xi in
                                            let ans = gen_expr so (combine xi lxi) ((combine lxi vi)@sn1) en1 in
                                                stacksize := !stacksize -1; ans
                                | String _ -> let xi,en1 = assoc ("String",f) !implementation in
                                              let lxi = map newloc xi in
                                              let ans=gen_expr so (combine xi lxi) ((combine lxi vi)@sn1) en1 in
                                                stacksize := !stacksize -1 ;ans
                                | Void -> (print_string (String.concat "" ["ERROR: " ; (string_of_int i) ; ": Case on void"]) ; exit 1;))
        | EXPR (i,DispatchEx (Some e0,None,IDENT (_,f),l)) -> (* still missing dispatch on primitive/void *)
                        stacksize := 1+ !stacksize;
                        if !stacksize = 1000 then (print_string (String.concat "" ["ERROR: " ; (string_of_int i) ; ": stackoverflow"]) ; exit 1;) else
                        let (vi,sn1) = vals so env ([],store) l in
                        let (v0,sn2) = gen_expr so env sn1 e0 in
                        (match !v0 with Object (x,aili) ->
                                let xi,en1 = assoc (x,f) !implementation in
                                let lxi = map newloc xi in
                                  gen_expr v0 ((combine xi lxi)@aili) ((combine lxi (List.rev vi))@sn2) en1
                                | Int _ -> let xi,en1 = assoc ("Int",f) !implementation in
                                           let lxi = map newloc xi in
                                           let ans = gen_expr v0 (combine xi lxi) ((combine lxi vi)@sn2) en1 in
                                                stacksize := !stacksize -1 ;ans
                                | Bool _ -> let xi,en1 = assoc ("Bool",f) !implementation in
                                            let lxi = map newloc xi in
                                            let ans = gen_expr v0 (combine xi lxi) ((combine lxi vi)@sn2) en1 in
                                                stacksize := !stacksize -1 ;ans
                                | String _ -> let xi,en1 = assoc ("String",f) !implementation in
                                              let lxi = map newloc xi in
                                              let ans = gen_expr v0 (combine xi lxi) ((combine lxi vi)@sn2) en1 in
                                                stacksize := !stacksize -1 ;ans
                                | Void -> (print_string (String.concat "" ["ERROR: " ; (string_of_int i) ; ": Case on void"]) ; exit 1;))
        | EXPR (i,DispatchEx (Some e0,Some (CoolType (_,t)),IDENT (_,f),l)) ->
                        stacksize := 1+ !stacksize;
                        if !stacksize = 1000 then (print_string (String.concat "" ["ERROR: " ; (string_of_int i) ; ": stackoverflow"]) ; exit 1;) else
                        let (vi,sn1) = vals so env ([],store) l in
                        let (v0,sn2) = gen_expr so env sn1 e0 in
                        (match !v0 with Object (x,aili) ->
                                let xi,en1 = assoc (t,f) !implementation in
                                let lxi = map newloc xi in
                                  gen_expr v0 ((combine xi lxi)@aili) ((combine lxi vi)@sn2) en1
                                | Int _ -> let xi,en1 = assoc ("Int",f) !implementation in
                                           let lxi = map newloc xi in
                                           let ans = gen_expr v0 (combine xi lxi) ((combine lxi vi)@sn2) en1 in
                                                stacksize := !stacksize -1 ;ans
                                | Bool _ -> let xi,en1 = assoc ("Bool",f) !implementation in
                                            let lxi = map newloc xi in
                                            let ans = gen_expr v0 (combine xi lxi) ((combine lxi vi)@sn2) en1 in
                                                stacksize := !stacksize -1 ;ans
                                | String _ -> let xi,en1 = assoc ("String",f) !implementation in
                                              let lxi = map newloc xi in
                                              let ans =gen_expr v0 (combine xi lxi) ((combine lxi vi)@sn2) en1 in
                                                stacksize := !stacksize -1 ;ans
                                | Void -> (print_string (String.concat "" ["ERROR: " ; (string_of_int i) ; ": Case on void"]) ; exit 1;))
        | EXPR (i,IfEx (e1,e2,e3)) ->
                        let (b,s2) = gen_expr so env store e1 in
                          gen_expr so env s2 (match !b with
                            | Bool true ->  e2
                            | Bool false -> e3
                            | _ -> failwith "not a bool? what? broken typechecker?" )
        | EXPR (i, BlockEx xs) -> 
                        List.fold_left (fun (v, store) ->
                                gen_expr so env store
                        ) (so, store) xs
        | EXPR (i,LetEx ([],e2)) -> gen_expr so env store e2
        | EXPR (i,LetEx (((IDENT (_,id),CoolType (_,t),None)::xs),e2)) ->
                        let v = default t in
                        let l1 = newloc () in
                        gen_expr so ((id,l1)::env) ((l1,v)::store) (EXPR (i,LetEx (xs,e2)))
        | EXPR (i,LetEx (((IDENT(_,id),t,Some e1)::xs),e2)) ->
                        let (v1,s2) = gen_expr so env store e1 in
                        let l1 = newloc () in
                        gen_expr so ((id,l1)::env) ((l1,v1)::s2) (EXPR (i,LetEx (xs,e2)))
        | EXPR (i,CaseEx (e0,l)) ->
			let v0,s2 = gen_expr so env store e0 in
			let x = match !v0 with
			  | Object (s,_) -> s
			  | Int _ -> "Int"
			  | Bool _ -> "Bool"
			  | String _ -> "String"
                          | Void -> (print_string (String.concat "" ["ERROR: " ; (string_of_int i) ; ": Case on void"]) ; exit 1;)in
			let loc = newloc () in
			let anc = try closestancestor x (map (fun (_,CoolType (_,t),_) -> t) l) with 
                                Failure _ -> (print_string (String.concat "" ["ERROR: " ; (string_of_int i) ; ": Case nobr"]) ; exit 1;)in
			let (IDENT (_,xi)),ti,ei = find (fun (_,CoolType (_,t),_) -> t = anc) l in
			  gen_expr so ((xi,loc)::env) ((loc,v0)::s2) ei
        | EXPR (i,LoopEx (b,e)) ->
                        let (v,s2) = gen_expr so env store b in
                        (match !v with
                          | Bool false -> (ref Void, s2)
                          | Bool true -> let (v2,s3) = gen_expr so env s2 e in
                                                 gen_expr so env s3 (EXPR (i,LoopEx (b,e)))
                          | _ -> failwith "check your typechecker")
        | EXPR (i,IsVdEx e) ->
                        let (v,s) = gen_expr so env store e in
                        (match !v with
                          | Void -> (ref (Bool true),s)
                          | _ -> (ref (Bool false),s))
        | EXPR (i,UnOpEx (Neg,e)) ->
                        let (v,s) = gen_expr so env store e in
                        (match !v with Int i -> (ref (Int (neg i)),s))
        | EXPR (i,UnOpEx (Not,e)) ->
                        let (v,s) = gen_expr so env store e in
                        (match !v with Bool b -> (ref (Bool (not b)),s))
        | EXPR (i,BinOpEx (o,e1,e2)) ->
                        let (i1',s2) = gen_expr so env store e1 in
                        let (i2',s3) = gen_expr so env s2 e2 in
                        let (Int i1,Int i2) = (!i1',!i2') in
                          (try (ref (Int (o i1 i2)), s3) with Division_by_zero -> (print_string (String.concat "" ["ERROR: " ; (string_of_int i) ; ": / by 0"]); exit 1;))
        | EXPR (i,CmpOpEx (o,e1,e2)) ->
                        let v1,s2 = gen_expr so env store e1 in
                        let v2,s3 = gen_expr so env s2 e2 in
                        (ref (Bool (match o with
                          | Le -> begin
                                    match !v1,!v2 with
                                      | (Int i1, Int i2) -> i1 <= i2
                                      | (Bool b1, Bool b2) -> b1 <= b2
                                      | (String s1, String s2) -> s1 <= s2
                                      | _ -> false
                                  end
                          | Lt -> begin
                                    match !v1,!v2 with
                                      | (Int i1, Int i2) -> i1 < i2
                                      | (Bool b1, Bool b2) -> b1 < b2
                                      | (String s1, String s2) -> s1 < s2
                                      | _ -> false
                                  end
                          | Eq -> begin
                                    match !v1,!v2 with
                                      | (Int i1, Int i2) -> i1 = i2
                                      | (Bool b1, Bool b2) -> b1 = b2
                                      | (String s1, String s2) -> s1 = s2
                                      | _ -> v1 == v2
                          end)),s3)
        | EXPR (0, Internal "Object.abort") -> print_string "abort\n"; exit 0;
        | EXPR (0, Internal "Object.copy") -> begin match !so with 
                | Object (t,attrs) -> let e,s = List.split (map (fun (s,i) -> let l = newloc () in let o = assoc i store in (s,l),(l,o)) attrs) in
                (ref (Object (t,e)),(s@store))
                | _ -> (so,store)
        end
        | EXPR (0, Internal "Object.type_name") -> gen_expr so env store (EXPR (0,ConstantEx (STRING (match !so with
                | Object (s,_) -> s
                | Int _ -> "Int"
                | String _ -> "String"
                | Bool _ -> "Bool"
                | Void -> failwith "dispatch on vvoid check failed"
        ))))
        | EXPR (0, Internal "IO.out_string") -> let (thestr ,s') = gen_expr so env store (EXPR (0, ConstantEx (ID (IDENT (0,"x"))))) in let (String x) = !thestr in print_string x; (so,s')
        | EXPR (0, Internal "IO.out_int") -> let (theint,s') = gen_expr so env store (EXPR (0, ConstantEx (ID (IDENT (0,"x"))))) in let (Int x) = !theint in print_string (to_string x); (so,s')
        | EXPR (0, Internal "IO.in_string") -> (let s = read_line () in try Str.search_forward (Str.regexp_string "\000") s 0; ref (String "") with Not_found -> ref (String s)),store
        | EXPR (0, Internal "IO.in_int") -> ((try ref (Int (of_int (read_int ()))) with Failure _ -> ref (Int 0l)),store)
        | EXPR (0, Internal "String.length") -> let (String x) = !so in (ref (Int (of_int (String.length x))),store)
        | EXPR (0, Internal "String.concat") -> let (thestr,s') = gen_expr so env store (EXPR (0, ConstantEx (ID (IDENT (0,"s"))))) in let (String x) = !thestr in (match !so with String me -> (ref (String (String.concat "" [me; x])), s'))
        | EXPR (0, Internal "String.substr") ->
                        let (thei,s') = gen_expr so env store (EXPR (0, ConstantEx (ID (IDENT (0,"i"))))) in 
                        let (thel,s'') = gen_expr so env s' (EXPR (0, ConstantEx (ID (IDENT (0,"l"))))) in
                        let (Int i, Int l) = (!thei,!thel) in
                        let (String me) = !so in 
                        (try ref (String (String.sub me (to_int l) (to_int i))), s''
                        with Invalid_argument _ -> 
                           (print_string (String.concat "" ["ERROR: " ; "0" ; ": Exception: String.substr out of range"]); exit 1;))
        | EXPR (_, Internal _ ) -> failwith "empty stdlib"
        | EXPR (_, DispatchEx (None, Some _, _, _)) -> failwith "invalid dispatch"

(*This holds the list of strings that's been read in. The AST *)
let arg = ref [];;

(* below here just input code to read in the annotated AST *)
let readInput func =
  let inFile = open_in Sys.argv.(1) in
  try
    while true do
      let line = input_line inFile in
      func line
    done
  with End_of_file ->
    close_in inFile ;;

let rec iterate n f arg =
  if n = 0 then (function x -> x)
  else f (iterate (n-1) f) ;;


let rec

readExpr () = let n = int_of_string (hd !arg) in
              let t = hd (tl !arg) in
              (arg:= tl (tl !arg); TypedExpr (n,t, readAnExpr ()))

and

readN : 'a. int -> (unit -> 'a) -> 'a list = fun n f -> match n with
        | 0 -> []
        | _ -> ((f ()) :: readN (n-1) f)

and

readList : 'a. (unit -> 'a) -> 'a list = fun f -> List.rev (let n = int_of_string (hd !arg) in ((arg:= tl !arg); readN n f))

and

readMPAttr () = let first = List.nth !arg 1 in
                let second = List.nth !arg 2 in
                (match hd !arg with
  | "initializer" -> Attr (first,second,(arg := tl (tl (tl !arg)); readExpr () ))
  | "no_initializer" -> let ans = AttrNI (first,second) in (arg := tl (tl (tl !arg)); ans)
)

and
       
readMapClass () = reverse2 ((arg := tl !arg; readList readMPAttr), (hd !arg))

and

readClassMap : unit -> classMap = fun () -> ((arg := tl !arg; readList readMapClass))

and

readImpMap () = reverse2 ((arg := tl !arg; readList readMethodImp),(hd !arg))

and

readMethodImp : unit -> methodImp = fun () ->
  let (name :: num :: text) = !arg in
  let (attrs,inter) = split (int_of_string num) text in
  (arg:= tl inter); MethodImp (name,attrs,hd inter,(readExpr ()))

and

readParentMap () =  arg := tl !arg; (readList readParentRel)

and

readParentRel () = let t = hd (tl !arg) in
                   let h = hd !arg in
                   ((arg := tl (tl !arg)); (h,  t))

and 

readFeature : unit -> feature = fun () -> match (hd !arg) with 
  | "method" -> (arg := tl !arg; readMethod ())
  | _ -> Attribute (readAttr ())

and

readAttr () = let t = hd !arg in (arg := tl !arg; match t with
  | "attribute_no_init" -> let id = readIdentifer () in
                           let t = readType () in
                           AttrNoInit (id,t)
  | _ -> let id = readIdentifer () in
         let t = readType () in
         let e = readExpr () in 
         AttrInit (id,t,e)
)

and

readMethod () = let id = readIdentifer () in
                let formals = readList readFormal in
                let t = readType () in
                let e = readExpr () in
                Method (CoolMethod (id,formals,t,e))

and

readFormal () = let id = readIdentifer () in (id , readType ())

and

readInheritance () = match hd !arg with 
  | "no_inherits" -> None
  | _ -> arg := tl !arg; Some readType

and

readAnExpr () = match (hd !arg) with
  | "assign"                                                  -> (arg := tl !arg); readAssignment ()
  | "integer" | "string" | "identifier" | "true" | "false"    -> readConstant ()
  | "if"                                                      -> (arg := tl !arg); readIf ()
  | "while"                                                   -> (arg := tl !arg); readWhile ()
  | "block"                                                   -> (arg := tl !arg); readBlock ()
  | "new"                                                     -> (arg := tl !arg); readNew ()
  | "isvoid"                                                  -> (arg := tl !arg); readIsVoid ()
  | "plus" | "minus" | "times" | "divide"                     -> readBinOp ()
  | "lt" | "le" | "eq"                                        -> readCmpOp ()
  | "not" | "negate"                                          -> readUnOp ()
  | "let"                                                     -> (arg := tl !arg); readLet ()
  | "case"                                                    -> (arg := tl !arg); readCase ()
  | "self_dispatch" | "dynamic_dispatch" | "static_dispatch"  -> readDispatch ()
  | "internal"                                                -> (arg := tl !arg); readInternal ()
  | _                                                         -> raise (Failure "Unmatched expression")

and

readInternal () = let v = hd !arg in ((arg:= tl !arg); Internal v)

and

readIf () =
  let ifCond = readExpr () in
  let trueBody = readExpr () in
  let falseBody = readExpr () in
    IfEx (ifCond , trueBody , falseBody)

and

readWhile () =
  let loopCond = readExpr () in
  let loopBody = readExpr () in
  LoopEx (loopCond, loopBody)

and

readConstant () =
  let const = (hd !arg) in arg := (tl !arg);
  let n = Str.regexp_string "\\n" in
  let t = Str.regexp_string "\\t" in
  let strfn x = Str.global_replace n "\n" (Str.global_replace t "\t" x) in
  match const with
    | "integer"     -> let const = (hd !arg) in arg := (tl !arg); ConstantEx (INT (of_string const))
    | "string"      -> let const = (hd !arg) in arg := (tl !arg); ConstantEx (STRING (strfn const))
    | "identifier"  -> ConstantEx (ID (readIdentifer ()))
    | "true"        -> ConstantEx T
    | "false"       -> ConstantEx F
    | _             -> raise (Failure "Scorn on OCAML error messages")

and

readAssignment () =
  let ident = readIdentifer () in
  let expr  = readExpr () in
  AssignmentEx (ident, expr)

and

readBlock () = BlockEx (readList readExpr)

and

readNew () = NewTypeEx (readType ())

and

readIsVoid () = IsVdEx (readExpr ())

and

readBinOp () =
  let operation = (hd !arg) and argument1 = (arg := tl !arg;readExpr ())  and argument2 = readExpr ()  in
  match operation with
  | "plus"    -> BinOpEx (add, argument1, argument2)
  | "minus"   -> BinOpEx (sub, argument1, argument2)
  | "times"   -> BinOpEx (mul, argument1, argument2)
  | "divide"  -> BinOpEx (div, argument1, argument2)
  | _         -> raise (Failure "Unmatched Binary Operation")

and

readCmpOp () =
  let operation = (hd !arg) and argument1 = (arg := tl !arg; readExpr ()) and argument2 = readExpr () in
  match operation with
  | "le"      -> CmpOpEx (Le, argument1, argument2)
  | "lt"      -> CmpOpEx (Lt, argument1, argument2)
  | "eq"      -> CmpOpEx (Eq, argument1, argument2)
  | _         -> raise (Failure "Unmatched Comparative Operation")

and

readUnOp () =
  let operation = (hd !arg) and argument = (arg := tl !arg; readExpr ()) in
  match operation with
  | "not"     -> UnOpEx (Not, argument)
  | "negate"  -> UnOpEx (Neg, argument)
  | _         -> raise (Failure "Unmatched Unitary Operation")

and

readLet () = let bindinglist = readList readLocalBinding in
             LetEx (bindinglist, readExpr ())

and

readLocalBinding () =
  let bindType = (hd !arg) in arg := (tl !arg);
  let id = readIdentifer () in
  let t = readType () in
  match bindType with
  | "let_binding_no_init"   -> (id, t, None)
  | "let_binding_init"      -> (id, t, Some (readExpr ()))
  | _                       -> failwith "Unmatched let binding"

and

readCase () = let e = readExpr () in CaseEx (e, readList readCaseBranch)

and

readCaseBranch () =
  let caseIdent = readIdentifer () in
  let caseType = readType () in
  let caseExpr = readExpr () in
  (caseIdent, caseType, caseExpr)

and

readDispatch () =
  let typeDispatch = (hd !arg) in arg := (tl !arg);
  match typeDispatch with
  | "dynamic_dispatch"              -> readDynamicDispatch ()
  | "static_dispatch"               -> readStaticDispatch ()
  | "self_dispatch"                 -> readSelfDispatch ()
  | _                               -> failwith "unmateched dispatch statement"

and

readStaticDispatch () =
  let callerExpr = readExpr () in
  let theType = readType () in
  let methodName = readIdentifer () in
  let methodParameters = readList readExpr in
  DispatchEx (Some callerExpr, Some theType, methodName, methodParameters)

and

readDynamicDispatch () =
  let callerExpr = readExpr () in
  let methodName = readIdentifer () in
  let methodParameters = readList readExpr in
  DispatchEx (Some callerExpr, None, methodName, methodParameters)

and

readSelfDispatch () =
  let methodName = readIdentifer () in
  let methodParameters = readList readExpr in
  DispatchEx (None, None, methodName, methodParameters)

and

readType () =
  let lineNo = (hd !arg) and name = hd (tl !arg) in
  arg := (tl (tl !arg));
  CoolType (int_of_string lineNo, name)

and

readIdentifer () =
  let lineNo = (hd !arg) and name = hd (tl !arg) in
  arg := (tl (tl !arg));
  IDENT (int_of_string lineNo, name)


let readMaps () = (readParentMap (),((arg:= tl !arg);readList readImpMap), readClassMap ())

(*let main () = readInput print_endline ;;*)

let unimp = (function MethodImp (name,attrs,impl,e) -> (name,(attrs,e)))

let main () = readInput (fun x -> arg := (x :: !arg));
              arg := List.rev !arg;
              let (pm,im,cm) = readMaps () in
( classmap := cm;
  parentmap := pm;
  implementation := concat (map (function (x,ms) -> map (function (a,b) -> ((x,a),b)) (map unimp ms)) im);
  gen_expr (ref Void) [] [] (EXPR (0,(DispatchEx (Some (EXPR (0,NewTypeEx (CoolType (0,"Main")))),None,(IDENT (0,"main")),[]))))
)
;;

main ()
