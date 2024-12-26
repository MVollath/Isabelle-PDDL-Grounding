theory Utils
  imports
    "Propositional_Proof_Systems.Sema"
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
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

(* random lemmas *)

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

subsection \<open> Static predicates \<close>



definition fmla_preds :: "'ent atom formula \<Rightarrow> predicate set" where
  "fmla_preds F = {p | p xs. predAtm p xs \<in> atoms F}"
lemma fmla_preds_simps [simp]:
  "fmla_preds (Atom (predAtm p xs)) = {p}"
  "fmla_preds (Atom (Eq a b)) = {}"
  "fmla_preds \<bottom> = {}"
  "fmla_preds (\<^bold>\<not> F) = fmla_preds F"
  "fmla_preds (F1 \<^bold>\<and> F2) = fmla_preds F1 \<union> fmla_preds F2"
  "fmla_preds (F1 \<^bold>\<or> F2) = fmla_preds F1 \<union> fmla_preds F2"
  "fmla_preds (F1 \<^bold>\<rightarrow> F2) = fmla_preds F1 \<union> fmla_preds F2"
    apply (force simp: fmla_preds_def)
   apply (force simp: fmla_preds_def)
   apply (force simp: fmla_preds_def)
   apply (force simp: fmla_preds_def)
   apply (force simp: fmla_preds_def)
   apply (force simp: fmla_preds_def)
  apply (force simp: fmla_preds_def)
  done

lemma "p \<notin> fmla_preds F \<Longrightarrow> predAtm p xd \<notin> atoms F"
  by (simp add: fmla_preds_def)

lemma map_preserves_fmla_preds: "fmla_preds F = fmla_preds ((map_formula \<circ> map_atom) f F)"
proof (induction F)
  case (Atom x)
  thus ?case by (cases x) simp_all
qed auto


thm irrelevant_atom

subsection \<open> STRIPS Formulas \<close>

text \<open>The lemma \<open>pn_atoms_updates\<close> is in a very unfortunate form, so I have to split it.\<close>

lemma prod_unions_alt: "prod_unions (a, b) (c, d) = (a \<union> c, b \<union> d)"
  using prod_unions_def by auto

lemma snd_prod_unions: "snd (prod_unions A B) = snd A \<union> snd B"
  apply (induction A; induction B)
  by (simp_all add: prod_unions_alt)

lemma fst_prod_unions: "fst (prod_unions A B) = fst A \<union> fst B"
  apply (induction A; induction B)
  by (simp_all add: prod_unions_alt)

lemma pn_atoms_updates_split: "(p \<notin> snd (pn_atoms F) \<longrightarrow>
    ((M \<Turnstile> F \<longrightarrow> M(p := True) \<Turnstile> F)
    \<and> (\<not>(M \<Turnstile> F) \<longrightarrow> \<not>M(p := False) \<Turnstile> F))) \<and>
   (p \<notin> fst (pn_atoms F) \<longrightarrow>
    ((M \<Turnstile> F \<longrightarrow> M(p := False) \<Turnstile> F)
    \<and> (\<not>(M \<Turnstile> F) \<longrightarrow> \<not>M(p := True) \<Turnstile> F)))"
  (is "(?notn \<longrightarrow> (?A F\<and> ?B)) \<and> (?notp \<longrightarrow> (?C \<and> ?D))")
proof (induction F)
  case (And F1 F2)
    (* TODO: can I just use "intro conjI; intro: impI" here to automatically create assumptions and split the goal? *)
  { assume "p \<notin> snd (pn_atoms (F1 \<^bold>\<and> F2))"
    hence "p \<notin> snd (pn_atoms F1) \<and> p \<notin> snd (pn_atoms F2)"
      using snd_prod_unions pn_atoms.simps(4) by (metis UnCI)
    hence "(M \<Turnstile> F1 \<^bold>\<and> F2 \<longrightarrow> M(p := True) \<Turnstile> F1 \<^bold>\<and> F2) \<and> (\<not> M \<Turnstile> F1 \<^bold>\<and> F2 \<longrightarrow> \<not> M(p := False) \<Turnstile> F1 \<^bold>\<and> F2)"
      using And.IH formula_semantics.simps(4) by blast }
  moreover { assume "p \<notin> fst (pn_atoms (F1 \<^bold>\<and> F2))"
    hence "p \<notin> fst (pn_atoms F1) \<and> p \<notin> fst (pn_atoms F2)"
      using fst_prod_unions pn_atoms.simps(4) by (metis UnCI)
    hence "(M \<Turnstile> F1 \<^bold>\<and> F2 \<longrightarrow> M(p := False) \<Turnstile> F1 \<^bold>\<and> F2) \<and> (\<not> M \<Turnstile> F1 \<^bold>\<and> F2 \<longrightarrow> \<not> M(p := True) \<Turnstile> F1 \<^bold>\<and> F2)"
      using And.IH formula_semantics.simps(4) by blast }
  ultimately show ?case by blast
next
  case (Or F1 F2)
  { assume "p \<notin> snd (pn_atoms (F1 \<^bold>\<or> F2))"
    hence "p \<notin> snd (pn_atoms F1) \<and> p \<notin> snd (pn_atoms F2)"
      using snd_prod_unions pn_atoms.simps(5) by (metis UnCI)
    hence "(M \<Turnstile> F1 \<^bold>\<or> F2 \<longrightarrow> M(p := True) \<Turnstile> F1 \<^bold>\<or> F2) \<and> (\<not> M \<Turnstile> F1 \<^bold>\<or> F2 \<longrightarrow> \<not> M(p := False) \<Turnstile> F1 \<^bold>\<or> F2)"
      using Or.IH formula_semantics.simps(5) by blast }
  moreover { assume "p \<notin> fst (pn_atoms (F1 \<^bold>\<or> F2))"
    hence "p \<notin> fst (pn_atoms F1) \<and> p \<notin> fst (pn_atoms F2)"
      using fst_prod_unions pn_atoms.simps(5) by (metis UnCI)
    hence "(M \<Turnstile> F1 \<^bold>\<or> F2 \<longrightarrow> M(p := False) \<Turnstile> F1 \<^bold>\<or> F2) \<and> (\<not> M \<Turnstile> F1 \<^bold>\<or> F2 \<longrightarrow> \<not> M(p := True) \<Turnstile> F1 \<^bold>\<or> F2)"
      using Or.IH formula_semantics.simps(5) by blast }
  ultimately show ?case by blast
next
  case (Imp F1 F2)
  note Imp.IH
  { assume "p \<notin> snd (pn_atoms (F1 \<^bold>\<rightarrow> F2))"
    hence "p \<notin> fst (pn_atoms F1) \<and> p \<notin> snd (pn_atoms F2)"
      using snd_prod_unions pn_atoms.simps(6) UnCI by (metis snd_swap)
    hence "(M \<Turnstile> F1 \<^bold>\<rightarrow> F2 \<longrightarrow> M(p := True) \<Turnstile> F1 \<^bold>\<rightarrow> F2) \<and> (\<not> M \<Turnstile> F1 \<^bold>\<rightarrow> F2 \<longrightarrow> \<not> M(p := False) \<Turnstile> F1 \<^bold>\<rightarrow> F2)"
      using Imp.IH formula_semantics.simps(6) by blast }
  moreover { assume "p \<notin> fst (pn_atoms (F1 \<^bold>\<rightarrow> F2))"
    hence "p \<notin> snd (pn_atoms F1) \<and> p \<notin> fst (pn_atoms F2)"
      using fst_prod_unions pn_atoms.simps(6) UnCI by (metis fst_swap)
    hence "(M \<Turnstile> F1 \<^bold>\<rightarrow> F2 \<longrightarrow> M(p := False) \<Turnstile> F1 \<^bold>\<rightarrow> F2) \<and> (\<not> M \<Turnstile> F1 \<^bold>\<rightarrow> F2 \<longrightarrow> \<not> M(p := True) \<Turnstile> F1 \<^bold>\<rightarrow> F2)"
      using Imp.IH formula_semantics.simps(6) by blast }
  ultimately show ?case by blast
qed simp_all

(* this now follows *)
thm pn_atoms_updates
lemma "p \<notin> snd (pn_atoms F) \<Longrightarrow> n \<notin> fst (pn_atoms F) \<Longrightarrow>
  ((M \<Turnstile> F \<longrightarrow> (M(p := True) \<Turnstile> F \<and> M(n := False) \<Turnstile> F)))
\<and> ((\<not>(M \<Turnstile> F)) \<longrightarrow> \<not>(M(n := True) \<Turnstile> F) \<and> \<not>(M(p := False) \<Turnstile> F))"
  using pn_atoms_updates_split by metis

lemma p_atoms_updates:
  assumes "p \<notin> snd (pn_atoms F)"
  shows "M \<Turnstile> F \<longrightarrow> M(p := True) \<Turnstile> F"
        "\<not>(M \<Turnstile> F) \<longrightarrow> \<not>M(p := False) \<Turnstile> F"
  apply (metis assms pn_atoms_updates_split)
  by (metis assms pn_atoms_updates_split)

lemma n_atoms_updates:
  assumes "p \<notin> fst (pn_atoms F)"
  shows "M \<Turnstile> F \<longrightarrow> M(p := False) \<Turnstile> F"
        "\<not>(M \<Turnstile> F) \<longrightarrow> \<not>M(p := True) \<Turnstile> F"
  apply (metis assms pn_atoms_updates_split)
  by (metis assms pn_atoms_updates_split)



end