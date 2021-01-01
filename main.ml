open RBT_height.RBT_height

let n = 200
let l = 200

let nat_of_int n = nat_of_integer (Z.of_int n)

let str_of_nat n = Z.to_string (integer_of_nat n)

let rec run i l = nat_upt (nat_of_int (i * l)) (nat_of_int ((i + 1) * l))

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
    un_nat_set cur rest

let _ = union n l
