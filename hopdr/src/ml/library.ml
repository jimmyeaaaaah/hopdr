exception TrueExc
exception FalseExc
exception IntegerOverflow
exception RecursionExceeded

let check_mx = ref 100000
let check_mn = ref (-100000)

let set_min () =
  check_mx := 2;
  check_mn := -1

let set_small () =
  check_mx := 6;
  check_mn := -5

let set_med () =
  check_mx := 151;
  check_mn := -150

let set_large () =
  check_mx := 100000;
  check_mn := -100000

let n_recursion = ref 0
let n_recursion_limit = ref 1000

let hopdr_count_recursion () =
  n_recursion := !n_recursion + 1;
  if !n_recursion > !n_recursion_limit then raise RecursionExceeded

let set_n_recursion_limit n = n_recursion_limit := n
let reset_n_recursion () = n_recursion := 0

let event_integer_overflow () =
  if !check_mx > 10 then check_mx := !check_mx / 2;
  if !check_mn < -10 then check_mn := !check_mn / 2

let event_stack_overflow () = ()

let rand_int (x, y) =
  let diff = !check_mx - !check_mn in
  let mn, mx =
    match (x, y) with
    | Some x, Some y -> (x, y)
    | Some x, None -> (x, x + diff)
    | None, Some y -> (y - diff, y)
    | None, None -> (!check_mn, !check_mx)
  in
  Random.int (mx - mn) + mn

let check_overflow f x y =
  try f x y with Invalid_argument _ -> raise IntegerOverflow

let ( + ) a b =
  if a > 0 && b > 0 && a > max_int - b then raise IntegerOverflow
  else if a < 0 && b < 0 && a < min_int - b then raise IntegerOverflow
  else a + b

let ( - ) a b =
  if b > 0 && a < min_int + b then raise IntegerOverflow
  else if b < 0 && a > max_int + b then raise IntegerOverflow
  else a - b

let ( * ) a b =
  if a = 0 || b = 0 then 0
  else if a = -1 && b = min_int then raise IntegerOverflow
  else if b = -1 && a = min_int then raise IntegerOverflow
  else if a > 0 && b > 0 && a > max_int / b then raise IntegerOverflow
  else if a < 0 && b < 0 && a < max_int / b then raise IntegerOverflow
  else if a > 0 && b < 0 && b < min_int / a then raise IntegerOverflow
  else if a < 0 && b > 0 && a < min_int / b then raise IntegerOverflow
  else a * b

let ( mod ) a b =
  let a' = a mod b in
  if a' < 0 then a' + b else a'

let loop f n =
  for i = 1 to n do
    Printf.printf "epoch %d...\n" i;
    reset_n_recursion ();
    try
      (* if it terminates, it means that the program is *NOT* safe *)
      let () = f () in
      raise FalseExc
    with
    | IntegerOverflow ->
        Printf.printf "int overflow";
        event_integer_overflow ()
    | Stack_overflow ->
        Printf.printf "stack overflow\n";
        event_stack_overflow ()
    | RecursionExceeded -> ()
    | TrueExc -> ()
  done

let hopdr_main f fail =
  let n_recs = [ 1000; 10000; 100000; 1000000; 10000000000 ] in
  let configs = [ set_min; set_small; set_med; set_large ] in
  List.iter
    (fun n_rec ->
      List.iter
        (fun config ->
          set_n_recursion_limit n_rec;
          config ();
          loop f 1000)
        configs)
    n_recs;
  fail ()

(*** The program body starts here! ***)
