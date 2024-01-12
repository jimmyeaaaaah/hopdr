exception TrueExc
exception FalseExc
exception IntegerOverflow

let check_mx = ref 100000
let check_mn = ref (-100000)

let event_integer_overflow () = 
  if !check_mx > 10 then check_mx := !check_mx / 2;
  if !check_mn < -10 then check_mn := !check_mn / 2

let rand_int (x, y) = 
  let mn = match x with 
    | Some(x) -> x
    | None -> !check_mn
  in
  let mx = match y with
    | Some(x) -> x
    | None -> !check_mx
  in 
    Random.int (mx - mn) + mn
    
let check_overflow f x y = try f x y with Invalid_argument _ -> raise IntegerOverflow

let ( + ) a b = 
  if a > 0 && b > 0 && a > max_int - b then
    raise IntegerOverflow
  else if a < 0 && b < 0 && a < min_int - b then
    raise IntegerOverflow
  else
    a + b

let ( - ) a b = 
  if b > 0 && a < min_int + b then
    raise IntegerOverflow
  else if b < 0 && a > max_int + b then
    raise IntegerOverflow
  else
    a - b
    
let ( * ) a b =
  if a = 0 || b = 0 then
    0
  else if a = -1 && b = min_int then
    raise IntegerOverflow
  else if b = -1 && a = min_int then
    raise IntegerOverflow
  else if a > 0 && b > 0 && a > max_int / b then
    raise IntegerOverflow
  else if a < 0 && b < 0 && a < max_int / b then
    raise IntegerOverflow
  else if a > 0 && b < 0 && b < min_int / a then
    raise IntegerOverflow
  else if a < 0 && b > 0 && a < min_int / b then
    raise IntegerOverflow
  else
    a * b

let ( mod ) a b =
  let a' = a mod b in
  if a' < 0 then a' + b else a'

