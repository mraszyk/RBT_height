# Comparing height of RBTs in Isabelle

This repository contains an artifact of an experiment showing
that approximating the size of an RBT by its black-node height is quite imprecise.

The theory `RBT_height.thy` contains a definition of the `i`-th set
of `l` integers (function `run`), a function
comparing the black-node heights of two RBTs used when computing their union
(function `compare_height_rbt`), and a monomorphized function
computing the union of two sets of integers (function `un_nat_set`).

The file `RBT_height.ml` contains the code exported from the theory
`RBT_height.thy` by Isabelle. It can be reproduced by running
`isabelle build -d '$AFP' -evD .` and `mv RBT_height.ocaml RBT_height.ml`
in the root directory of this repository.

The file `main.ml` runs an experiment computing the union of
`n` (set on line 3) sets of `l` (set on line 4) integers each.
The output consists of three columns. The first two columns show the sizes
of the two sets in each union of two sets and the third column
shows the result of comparing the black-node heights of the two RBTs
(`LT`, `GT`, or `EQ`).

In this experiment, the first set is never larger than the second one,
so manually redefining
```
let rec rbt_comp_union_with_key c f t1 t2 =
  folda (rbt_comp_insert_with_key c (fun k v w -> f k w v)) t1 t2;;
```
on line 662 in the verified code `RBT_height.ml`,
i.e., overriding the comparison result by `LT`,
results in a much better performance (a factor of 10x for `n = l = 200`).

## Requirements:
  - Isabelle2020
  - ocamlbuild with the package zarith installed (`opam install zarith`)
