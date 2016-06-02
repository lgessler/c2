open List

(*This holds the list of strings that's been read in. The AST *)
let arg = ref [];;

let read_input func =
  let inFile = open_in Sys.argv.(1) in
  try
    while true do
      let line = input_line inFile in
      func line
    done
  with End_of_file ->
    close_in inFile ;;


let main () = read_input (fun x -> arg := (x :: !arg));
              arg := List.rev !arg;
              print_tac (dead_code (List.map read_tac arg))

main ()

let read_tac arg = match arg with
 | [] => []

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

while not end of file
        read one line
        if line = "" or line[0] = "#" or line[0] = ";" then 
                skip    // comment
        words = split line by whitespace
        if words[0] = "label"
                answer += TAC_Label(words[1]) 
        else if words[0] = "jmp"
                answer += TAC_Jmp(words[1])
        else if ... // "bt", "return", "comment", etc. 
        // otherwise: x <- OP ... 
        else if words[2] = "+"
                answer += TAC_Plus(words[0], words[2], words[3])
        else if words[2] = "string"
                next_line = read one line
                answer += TAC_String(words[0], next_line) 
        else if ... // all other cases 
