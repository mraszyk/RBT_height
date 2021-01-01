open RBT_height.RBT_height

let n = 200
let l = 200

let nat_of_int n = nat_of_integer (Z.of_int n)

let str_of_nat n = Z.to_string (integer_of_nat n)

let str_of_compare = function
  | LT -> "LT"
  | GT -> "GT"
  | EQ -> "EQ"

let compare_height_set x y = match x, y with
  | RBT_set x, RBT_set y -> compare_height_rbt x y

let rec run i l = nat_set_upt (nat_of_int (i * l)) (nat_of_int ((i + 1) * l))

let gen size =
  let rec loop acc = function
    | 0 -> acc
    | size ->
        let n = Random.int 1000000 in
        loop (n :: acc) (size - 1)
  in loop [] size

let rec union n l =
  let cur = nat_set (run n l) in
  (* let cur = nat_set (List.map nat_of_int (gen l)) in *)
  if n = 0 then cur else
    let rest = union (n - 1) l in
    (* let _ = Printf.printf "%d %d %s\n" l (n * l) (str_of_compare (compare_height_set cur rest)) in *)
    un_nat_set cur rest

let _ = union n l
