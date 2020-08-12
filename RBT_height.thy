theory RBT_height
  imports "HOL-Library.Code_Target_Nat" "Containers.Containers" RBT_set_opt
begin

(* We define a type of sorted and distinct lists from which we can create an RBT more efficiently
   than using the built-in function for converting lists into sets. *)

typedef (overloaded) 'a sdlist = "{xs :: ('a :: ccompare) list.
  case ID CCOMPARE('a) of None \<Rightarrow> xs = [] | Some _ \<Rightarrow> linorder.sorted cless_eq xs \<and> distinct xs}"
  by (auto intro!: exI[of _ "[]"] split: option.splits)
     (metis keys_eq_Nil_iff sorted_RBT_Set_keys)

setup_lifting type_definition_sdlist

lemma sset_rbt:
  fixes xs :: "('a :: ccompare) list"
    and c :: "'a comparator"
  assumes assms: "ID ccompare = Some c" "linorder.sorted cless_eq xs" "distinct xs"
  shows "ord.is_rbt cless (rbtreeify (map (\<lambda>x. (x, ())) xs))"
  using assms linorder.is_rbt_rbtreeify[OF ID_ccompare[OF assms(1)], of "map (\<lambda>x. (x, ())) xs"]
  by (auto simp: comp_def)

lift_definition sset :: "('a :: ccompare) sdlist \<Rightarrow> 'a set_rbt" is
  "\<lambda>xs. rbtreeify (map (\<lambda>x. (x, ())) xs)"
  using sset_rbt
  by fastforce

lemma Rep_sdlist_keys:
  fixes xs :: "('a :: ccompare) sdlist"
  shows "Rep_sdlist xs = RBT_Set2.keys (sset xs)"
  by transfer (auto simp: RBT_Impl.keys_def comp_def)

lemma rbt_comp_lookup_iff_in_set:
  fixes x :: "'a :: ccompare"
    and xs :: "'a list"
    and c :: "'a comparator"
  assumes "ID ccompare = Some c" "linorder.sorted cless_eq xs" "distinct xs"
  shows "rbt_comp_lookup ccomp (rbtreeify (map (\<lambda>x. (x, ())) xs)) x = Some () \<longleftrightarrow> x \<in> set xs"
  using linorder.rbt_lookup_rbtreeify[OF ID_ccompare[OF assms(1)], of "map (\<lambda>x. (x, ())) xs"]
      assms(2,3)
  by (auto simp: rbt_comp_lookup[OF ID_ccompare'[OF assms(1)]] assms(1) map_of_map_Pair_const
      comp_def)

lemma RBT_set_sset:
  fixes xs :: "('a :: ccompare) sdlist"
  shows "RBT_set (sset xs) = set (Rep_sdlist xs)"
  unfolding RBT_set_def
  apply transfer
  using rbt_comp_lookup_iff_in_set
  by (fastforce simp: rbtreeify_def split: option.splits)

lemma linorder_sorted_upt: "linorder.sorted (le_of_comp compare) [n..<n']"
proof -
  define c :: "nat comparator" where "c = compare"
  have cl: "class.linorder (le_of_comp c) (lt_of_comp c)"
    by (auto simp: c_def ID_ccompare ID_Some ccompare_nat_def)
  show ?thesis
    using linorder.sorted_sorted_wrt[OF cl] sorted_wrt_mono_rel[OF _ sorted_wrt_upt]
    by (auto simp: c_def ord_defs(1))
qed

lift_definition upt_sdlist :: "nat \<Rightarrow> nat \<Rightarrow> nat sdlist" is upt
  using linorder_sorted_upt
  by (auto simp: ID_Some ccompare_nat_def split: option.splits)

definition nat_set_upt :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "nat_set_upt i j = {i..<j}"

lemma nat_set_upt_code[code]: "nat_set_upt i j = RBT_set (sset (upt_sdlist i j))"
  by (auto simp: nat_set_upt_def RBT_set_sset upt_sdlist.rep_eq)

definition run :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "run i l = {i * l ..< Suc i * l}"

lemma run_code[code]: "run i l = nat_set_upt (i * l) (Suc i * l)"
  by (auto simp: run_def nat_set_upt_def)

definition compare_height_rbt :: "(nat, unit) mapping_rbt \<Rightarrow> (nat, unit) mapping_rbt \<Rightarrow>
  RBT_Impl.compare" where
  "compare_height_rbt t1 t2 =
    RBT_Impl.compare_height (RBT_Mapping2.impl_of t1) (RBT_Mapping2.impl_of t1)
    (RBT_Mapping2.impl_of t2) (RBT_Mapping2.impl_of t2)"

definition un_nat_set :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set" where
  "un_nat_set X Y = X \<union> Y"

definition int_nat_set :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set" where
  "int_nat_set X Y = X \<inter> Y"

export_code run compare_height_rbt un_nat_set int_nat_set
  nat_of_integer integer_of_nat RBT_set RBT_Impl.EQ
  in OCaml module_name RBT_height file_prefix "RBT_height_old"

declare Set_union_code(1)[code del]
declare rbt_union_code[code]
declare Set_inter_code(16)[code del]
declare rbt_inter_code[code]

(* Set_minus on RBTs not supported in Set_Impl! *)
declare Set_minus_code[code del]
declare rbt_minus_code[code]

export_code run compare_height_rbt un_nat_set int_nat_set
  nat_of_integer integer_of_nat RBT_set RBT_Impl.EQ
  in OCaml module_name RBT_height file_prefix "RBT_height_opt"

end