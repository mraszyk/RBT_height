open RBT_height.RBT_height

let n = 200
let l = 200

let nat_of_int n = nat_of_integer (Z.of_int n)

let gen size =
  let rec loop acc = function
    | 0 -> acc
    | size ->
        let n = Random.int 1000000 in
        loop (n :: acc) (size - 1)
  in loop [] size

let rec union n l g =
  let cur = g n in
  if n = 0 then cur else
    let rest = union (n - 1) l g in
    un_nat_set cur rest

let bench e s =
  let t1 = Unix.gettimeofday () in
  let _ = e () in
  let t2 = Unix.gettimeofday () in
  Printf.printf "%s: %fs\n" s (t2 -. t1)

let rec run i l = nat_upt (nat_of_int (i * l)) (nat_of_int ((i + 1) * l))
let sseq = nat_set (run 0 100000)
let srnd = nat_set (List.map nat_of_int (gen 100000))
let exp1 x = un_nat_set sseq srnd
let exp2 x = inter_nat_set sseq srnd
let exp3 x = union n l (fun n -> nat_set (run n l))
let exp4 x = union n l (fun n -> nat_set (List.map nat_of_int (gen l)))

let _ = bench exp1 "un_nat_set"
let _ = bench exp2 "inter_nat_set"
let _ = bench exp3 "union [..<]"
let _ = bench exp4 "union gen"
