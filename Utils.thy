theory Utils
imports "Propositional_Proof_Systems.Formulas"
begin

(* formula helpers *)

fun only_conj :: "'a formula \<Rightarrow> bool" where
  "only_conj (Atom a) \<longleftrightarrow> True" |
  "only_conj \<bottom> \<longleftrightarrow> True" |
  "only_conj (\<^bold>\<not> (Atom a)) \<longleftrightarrow> True" |
  "only_conj (\<phi> \<^bold>\<and> \<psi>) \<longleftrightarrow> only_conj \<phi> \<and> only_conj \<psi>" |

  "only_conj (\<^bold>\<not> _) \<longleftrightarrow> False" |
  "only_conj (_ \<^bold>\<or> _) \<longleftrightarrow> False" |
  "only_conj (_ \<^bold>\<rightarrow> _) \<longleftrightarrow> False"

fun disj_fmlas :: "'a formula list \<Rightarrow> 'a formula" where
  "disj_fmlas [] = Bot" |
  "disj_fmlas [f] = f" |
  "disj_fmlas (f # fs) = f \<^bold>\<or> disj_fmlas fs"

fun conj_fmlas :: "'a formula list \<Rightarrow> 'a formula" where
  "conj_fmlas [] = \<^bold>\<not> \<bottom>" |
  "conj_fmlas [f] = f" |
  "conj_fmlas (f # fs) = f \<^bold>\<and> conj_fmlas fs"

(* lemmas *)

(*
lemma map_of_SomeIn: "map_of m x = Some y \<Longrightarrow> y \<in> snd ` set m"
  by (metis image_eqI map_of_SomeD snd_conv)

lemma map_of_in_R_iff: "x \<in> fst ` set m \<longleftrightarrow> (\<exists>y. map_of m x = Some y \<and> y \<in> snd ` set m)"
  using map_of_SomeIn
  by (metis map_of_eq_None_iff not_None_eq)

lemma map_of_single_val:
  assumes "\<forall>y \<in> snd ` set m. y = z"
  shows "x \<in> fst ` set m \<longleftrightarrow> map_of m x = Some z"
  using assms
  by (metis domI domIff map_of_eq_None_iff map_of_in_R_iff)
*)

lemma map_of_in_R_iff: "x \<in> fst ` set m \<longleftrightarrow> (\<exists>y. map_of m x = Some y)"
  by (metis map_of_eq_None_iff not_None_eq)

lemma map_of_single_val:
  assumes "\<forall>(x, y) \<in> set m. y = z"
  shows "x \<in> fst ` set m \<longleftrightarrow> map_of m x = Some z"
  using assms map_of_in_R_iff
  by (metis (full_types) case_prodD map_of_SomeD)

lemma map_inj_dis:
  assumes "distinct xs" "inj f"
  shows "distinct (map f xs)"
  using assms distinct_map subset_inj_on by blast


(* rule rewriting *)

lemma conj_split_4:
  assumes "A \<and> B \<and> C \<and> D"
  shows "A" "B" "C" "D"
  using assms by simp_all

lemma conj_split_5:
  assumes "A \<and> B \<and> C \<and> D \<and> E"
  shows "A" "B" "C" "D" "E"
  using assms by simp_all

lemma conj_split_7:
  assumes "A \<and> B \<and> C \<and> D \<and> E \<and> F \<and> G"
  shows "A" "B" "C" "D" "E" "F" "G"
  using assms by simp_all

end