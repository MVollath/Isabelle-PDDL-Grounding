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


end