theory DNF
imports
    "Propositional_Proof_Systems.CNF"
    "Propositional_Proof_Systems.CNF_Formulas"
    "Propositional_Proof_Systems.CNF_Sema"
    "Propositional_Proof_Systems.CNF_Formulas_Sema"
    "Verified_SAT_Based_AI_Planning.CNF_Supplement"
    "Verified_SAT_Based_AI_Planning.CNF_Semantics_Supplement"
    Utils
begin

subsection \<open>DNF construction\<close>

fun is_conj where
  "is_conj (F \<^bold>\<and> G) \<longleftrightarrow> is_lit_plus F \<and> is_conj G" |
  "is_conj H \<longleftrightarrow> is_lit_plus H"

fun is_dnf where
  "is_dnf (F \<^bold>\<or> G) \<longleftrightarrow> is_dnf F \<and> is_dnf G" |
  "is_dnf H \<longleftrightarrow> is_conj H"

lemma lit_neg_lit:
  assumes "is_lit_plus F"
  shows "is_lit_plus (nnf (\<^bold>\<not> F))"
  using assms apply (induction F) apply simp_all
  using is_nnf_NotD by force

lemma disj_neg_conj:
  assumes "is_disj F"
  shows "is_conj (nnf (\<^bold>\<not> F))"
using assms proof (induction F)
  case Not then show ?case using is_nnf_NotD by fastforce
qed (auto simp add: lit_neg_lit)

lemma cnf_to_dnf:
  assumes "is_cnf F"
  shows "is_dnf (nnf (\<^bold>\<not> F))"
using assms proof (induction F)
  case Not
  then show ?case using is_nnf_NotD by fastforce
next
  case Or
  thus ?case using lit_neg_lit disj_neg_conj by auto
qed simp_all

definition "dnf F \<equiv> nnf (\<^bold>\<not> (cnf_form_of (nnf F)))"

lemma is_dnf_dnf: "is_dnf (dnf F)" unfolding dnf_def
  using is_nnf_nnf cnf_form_of_is cnf_to_dnf by blast

subsection \<open>Straight to transformation\<close>

primrec neg_of_lit where
"neg_of_lit (Pos k) = \<^bold>\<not>(Atom k)" |
"neg_of_lit (Neg k) = Atom k"

lemma neg_lit_semantics:
  "A \<Turnstile> form_of_lit l \<longleftrightarrow> \<not> A \<Turnstile> neg_of_lit l"
  by (cases l) simp_all

definition "neg_conj_of_clause c \<equiv> \<^bold>\<And>[neg_of_lit l. l \<leftarrow> c]"

lemma neg_conj_semantics: "A \<Turnstile> neg_conj_of_clause c \<longleftrightarrow> \<not> A \<Turnstile> disj_of_clause c"
proof -
  have "A \<Turnstile> disj_of_clause c \<longleftrightarrow> (\<exists>l \<in> set (map form_of_lit c). A \<Turnstile> l)"
    using disj_of_clause_def BigOr_semantics by metis
  also have "... \<longleftrightarrow> (\<exists>l \<in> set c. A \<Turnstile> form_of_lit l)"
    by simp
  also have "... \<longleftrightarrow> (\<exists>l \<in> set c. \<not>A \<Turnstile> neg_of_lit l)"
    using neg_lit_semantics by auto
  also have "... \<longleftrightarrow> \<not>(\<forall>l \<in> set c. A \<Turnstile> neg_of_lit l)"
    using neg_lit_semantics by auto
  also have "... \<longleftrightarrow> \<not>(\<forall>l \<in> set (map neg_of_lit c). A \<Turnstile> l)"
    by simp
  also have "... \<longleftrightarrow> \<not> A \<Turnstile> neg_conj_of_clause c"
    using neg_conj_of_clause_def BigAnd_semantics by metis
  finally show ?thesis by simp
qed

definition dnf_list :: "'a formula \<Rightarrow> 'a formula list" where
  "dnf_list F \<equiv> map (neg_conj_of_clause) (cnf_lists (nnf (\<^bold>\<not>F)))"

lemma dnf_list_semantics:
  fixes F :: "'a formula"
  shows "(A \<Turnstile> F) \<longleftrightarrow> (\<exists>c \<in> set (dnf_list F). A \<Turnstile> c)"
proof -
  define nF where "nF \<equiv> nnf (\<^bold>\<not>F)"
  have "A \<Turnstile> F \<longleftrightarrow> \<not> A \<Turnstile> nF"
    using nnf_semantics nF_def by force
  also have "... \<longleftrightarrow> \<not> A \<Turnstile> (form_of_cnf \<circ> cnf_lists) nF"
    using nF_def is_nnf_nnf cnf_form_semantics cnf_form_of_def by metis
  also have "... \<longleftrightarrow> \<not> A \<Turnstile> \<^bold>\<And>(map disj_of_clause (cnf_lists nF))"
    unfolding form_of_cnf_def by simp
  also have "... \<longleftrightarrow> \<not>(\<forall>c \<in> set (cnf_lists nF). A \<Turnstile> disj_of_clause c)"
    by simp
  also have "... \<longleftrightarrow> (\<exists>c \<in> set (cnf_lists nF). A \<Turnstile> neg_conj_of_clause c)"
    using neg_conj_semantics by auto
  also have "... \<longleftrightarrow> (\<exists>c \<in> set (map neg_conj_of_clause (cnf_lists nF)). A \<Turnstile> c)"
    using nF_def by simp
  finally show ?thesis using nF_def dnf_list_def by metis
qed




end