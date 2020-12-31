theory RBT_height
  imports "HOL-Library.Code_Target_Nat" "Containers.Containers" RBT_set_opt
begin

(* We define a type of sorted and distinct lists from which we can create an RBT more efficiently
   than using the built-in function for converting lists into sets. *)

typedef (overloaded) 'a sdlist = "{xs :: ('a :: ccompare) list.
  case ID CCOMPARE('a) of None \<Rightarrow> xs = []
  | Some c \<Rightarrow> linorder.sorted (le_of_comp c) xs \<and> distinct xs}"
  by (auto intro!: exI[of _ "[]"] split: option.splits)
     (metis keys_eq_Nil_iff sorted_RBT_Set_keys)

setup_lifting type_definition_sdlist

lemma sset_rbt:
  fixes xs :: "('a :: ccompare) list"
    and c :: "'a comparator"
  assumes assms: "ID ccompare = Some c" "linorder.sorted (le_of_comp c) xs" "distinct xs"
  shows "ord.is_rbt (lt_of_comp c) (rbtreeify (map (\<lambda>x. (x, ())) xs))"
  using assms linorder.is_rbt_rbtreeify[OF ID_ccompare[OF assms(1)], of "map (\<lambda>x. (x, ())) xs"]
  by (auto simp: comp_def)

lift_definition sset :: "('a :: ccompare) sdlist \<Rightarrow> 'a set_rbt" is
  "\<lambda>xs. rbtreeify (map (\<lambda>x. (x, ())) xs)"
  using sset_rbt
  by fastforce

lemma rbt_comp_lookup_iff_in_set:
  fixes x :: "'a :: ccompare"
    and xs :: "'a list"
    and c :: "'a comparator"
  assumes "ID ccompare = Some c" "linorder.sorted (le_of_comp c) xs" "distinct xs"
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

lemma quicksort_conv_sort_key:
  fixes f :: "'b \<Rightarrow> 'a :: ccompare"
  assumes "ID (ccompare :: 'a comparator option) = Some c"
  shows "ord.quicksort (lt_of_comp c) xs = linorder.sort_key (le_of_comp c) (\<lambda>x. x) xs"
  by (rule linorder.quicksort_conv_sort[OF ID_ccompare[OF assms]])

context linorder
begin

lemma distinct_remdups_adj: "sorted xs \<Longrightarrow> distinct (remdups_adj xs)"
  by (induction xs rule: remdups_adj.induct) auto

end

lift_definition sdlist_of_list :: "('a :: ccompare) list \<Rightarrow> 'a sdlist" is
  "\<lambda>xs :: 'a list. case ID CCOMPARE('a) of None \<Rightarrow> []
  | Some c \<Rightarrow> remdups_adj (ord.quicksort (lt_of_comp c) xs)"
  using linorder.sorted_remdups_adj[OF ID_ccompare linorder.sorted_sort[OF ID_ccompare]]
  using linorder.distinct_remdups_adj[OF ID_ccompare linorder.sorted_sort[OF ID_ccompare]]
  using quicksort_conv_sort_key
  by (fastforce split: option.splits)

lemma set_sdlist_of_list:
  fixes xs :: "('a :: ccompare) list"
    and c :: "'a comparator"
  assumes assms: "ID ccompare = Some c"
  shows "set (Rep_sdlist (sdlist_of_list xs)) = set xs"
  using assms
  apply transfer
  using linorder.set_sort[OF ID_ccompare] quicksort_conv_sort_key
  by fastforce

lemma set_code:
  fixes xs :: "('a :: ccompare) list"
  shows "set xs = (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''set: ccompare = None'')
    (\<lambda>_. set xs)
  | Some _ \<Rightarrow> RBT_set (sset (sdlist_of_list xs)))"
  by (auto simp: RBT_set_sset set_sdlist_of_list split: option.splits)

definition nat_set_upt :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "nat_set_upt i j = [i..<j]"

definition nat_set :: "nat list \<Rightarrow> nat set" where
  "nat_set = set"

definition un_nat_set :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set" where
  "un_nat_set X Y = X \<union> Y"

definition int_nat_set :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set" where
  "int_nat_set X Y = X \<inter> Y"

definition compare_height_rbt :: "(nat, unit) mapping_rbt \<Rightarrow> (nat, unit) mapping_rbt \<Rightarrow>
  RBT_Impl.compare" where
  "compare_height_rbt t1 t2 =
    RBT_Impl.compare_height (RBT_Mapping2.impl_of t1) (RBT_Mapping2.impl_of t1)
    (RBT_Mapping2.impl_of t2) (RBT_Mapping2.impl_of t2)"

export_code nat_set_upt nat_set un_nat_set int_nat_set
  nat_of_integer integer_of_nat compare_height_rbt RBT_set RBT_Impl.EQ
  in OCaml module_name RBT_height file_prefix "RBT_height_old"

declare Set_Impl.set_code[code del]
declare set_code[code]

declare Set_union_code(1)[code del]
declare rbt_union_code[code]
declare Set_inter_code(16)[code del]
declare rbt_inter_code[code]

(* Set_minus on RBTs not supported in Set_Impl! *)
declare Set_minus_code[code del]
declare rbt_minus_code[code]

export_code nat_set_upt nat_set un_nat_set int_nat_set
  nat_of_integer integer_of_nat compare_height_rbt RBT_set RBT_Impl.EQ
  in OCaml module_name RBT_height file_prefix "RBT_height_opt"

end
