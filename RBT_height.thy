theory RBT_height
  imports "HOL-Library.Code_Target_Nat" "Containers.Containers"
begin

definition run :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "run i l = {i * l ..< Suc i * l}"

definition compare_height_rbt :: "(nat, unit) mapping_rbt \<Rightarrow> (nat, unit) mapping_rbt \<Rightarrow>
  RBT_Impl.compare" where
  "compare_height_rbt t1 t2 =
    RBT_Impl.compare_height (RBT_Mapping2.impl_of t1) (RBT_Mapping2.impl_of t1)
    (RBT_Mapping2.impl_of t2) (RBT_Mapping2.impl_of t2)"

definition un_nat_set :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set" where
  "un_nat_set X Y = X \<union> Y"

export_code run compare_height_rbt un_nat_set nat_of_integer integer_of_nat RBT_set RBT_Impl.EQ
  in OCaml module_name RBT_height file_prefix "RBT_height"

end
