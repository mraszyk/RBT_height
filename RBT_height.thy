theory RBT_height
  imports "HOL-Library.Code_Target_Nat" "Containers.Containers" RBT_set_opt
begin

typedef (overloaded) 'a sdlist = "{xs :: ('a :: ccompare) list.
  case ID CCOMPARE('a) of None \<Rightarrow> xs = []
  | Some c \<Rightarrow> linorder.sorted (le_of_comp c) xs \<and> distinct xs}"
  by (auto intro!: exI[of _ "[]"] split: option.splits)
     (metis keys_eq_Nil_iff sorted_RBT_Set_keys)

setup_lifting type_definition_sdlist

lemma is_rbt_rbtreeify:
  fixes xs :: "('a :: ccompare) list"
    and c :: "'a comparator"
  assumes assms: "ID ccompare = Some c" "linorder.sorted (le_of_comp c) xs" "distinct xs"
  shows "ord.is_rbt (lt_of_comp c) (rbtreeify (map (\<lambda>x. (x, ())) xs))"
  using assms linorder.is_rbt_rbtreeify[OF ID_ccompare[OF assms(1)], of "map (\<lambda>x. (x, ())) xs"]
  by (auto simp: comp_def)

lift_definition rbt_of_sdlist :: "('a :: ccompare) sdlist \<Rightarrow> 'a set_rbt" is
  "\<lambda>xs. rbtreeify (map (\<lambda>x. (x, ())) xs)"
  using is_rbt_rbtreeify
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

lemma RBT_set_rbt_of_sdlist:
  fixes xs :: "('a :: ccompare) sdlist"
  shows "RBT_set (rbt_of_sdlist xs) = set (Rep_sdlist xs)"
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
  "\<lambda>xs. case ID CCOMPARE('a) of None \<Rightarrow> []
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

definition sset :: "'a list \<Rightarrow> 'a set" where
  "sset = set"

lemma sset_code[code]:
  fixes xs :: "('a :: ccompare) list"
  shows "sset xs = (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort (STR ''sset: ccompare = None'')
    (\<lambda>_. sset xs)
  | Some _ \<Rightarrow> RBT_set (rbt_of_sdlist (sdlist_of_list xs)))"
  by (auto simp: sset_def RBT_set_rbt_of_sdlist set_sdlist_of_list split: option.splits)

definition nat_upt :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "nat_upt i j = [i..<j]"

definition nat_set :: "nat list \<Rightarrow> nat set" where
  "nat_set = set"

definition nat_sset :: "nat list \<Rightarrow> nat set" where
  "nat_sset = sset"

definition un_nat_set :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set" where
  "un_nat_set X Y = X \<union> Y"

definition inter_nat_set :: "nat set \<Rightarrow> nat set \<Rightarrow> nat set" where
  "inter_nat_set X Y = X \<inter> Y"

export_code nat_upt nat_set nat_sset un_nat_set inter_nat_set nat_of_integer integer_of_nat
  in OCaml module_name RBT_height file_prefix "RBT_height_old"

declare Set_union_code(1)[code del]
declare rbt_union_code[code]
declare Set_inter_code(16)[code del]
declare rbt_inter_code[code]

(* Set_minus on RBTs not supported in Set_Impl! *)
declare Set_minus_code[code del]
declare rbt_minus_code[code]

export_code nat_upt nat_set nat_sset un_nat_set inter_nat_set nat_of_integer integer_of_nat
  in OCaml module_name RBT_height file_prefix "RBT_height_opt"

end