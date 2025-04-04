theory Formula_Utils
  imports "Propositional_Proof_Systems.Sema"
    "Propositional_Proof_Systems.CNF_Formulas"
begin

subsection \<open> pure conjunctions \<close>
(* Modeled after Propositional_Proof_Systems.CNF_Formulas.is_disj.
  A conjunction is a right deep tree e.g: A \<and> (\<not>B \<and> C) *)
term is_disj
fun is_conj where
  "is_conj (F \<^bold>\<and> G) \<longleftrightarrow> is_lit_plus F \<and> is_conj G" |
  "is_conj H \<longleftrightarrow> is_lit_plus H"

lemma map_preserves_isconj:
  assumes "is_conj F" shows "is_conj (map_formula m F)"
using assms proof (induction F)
  case (Not F)
  thus ?case by (cases F) simp_all
next
  case (And F G) thus ?case
  proof (cases F)
    case (Not a)
    thus ?thesis using And by (cases a) simp_all
  qed simp_all
qed simp_all

(* Like formula.And but it preserves the conjunct being a right-deep tree. *)
fun conjAnd :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" where
  "conjAnd \<bottom> B = \<bottom> \<^bold>\<and> B" |
  "conjAnd (\<^bold>\<not> \<bottom>) B = (\<^bold>\<not> \<bottom>) \<^bold>\<and> B" |
  "conjAnd (Atom a) B = (Atom a) \<^bold>\<and> B" |
  "conjAnd (\<^bold>\<not> (Atom a)) B = (\<^bold>\<not> (Atom a)) \<^bold>\<and> B" |
  "conjAnd (A1 \<^bold>\<and> A2) B = A1 \<^bold>\<and> conjAnd A2 B" |
  "conjAnd A B = A \<^bold>\<and> B"

text \<open> I struggle to correctly apply (induction ... rule: conjAnd.induct), so the following lemma
  helps to simplify it:\<close>
thm conjAnd.induct[of "\<lambda>x y. is_conj x \<and> is_conj y \<longrightarrow> is_conj (conjAnd x y)"]
lemma conjAnd_induct_isconj:
  fixes Q :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> bool"
  assumes "is_conj A \<and> is_conj B"
  shows "(\<And>B. is_conj B \<Longrightarrow> Q \<bottom> B) \<Longrightarrow>
    (\<And>B. is_conj B \<Longrightarrow> Q (\<^bold>\<not> \<bottom>) B) \<Longrightarrow>
    (\<And>a B. is_conj B \<Longrightarrow> Q (Atom a) B) \<Longrightarrow>
    (\<And>a B. is_conj B \<Longrightarrow> Q (\<^bold>\<not> (Atom a)) B) \<Longrightarrow>
    (\<And>A1 A2 B.
      (is_conj A2 \<Longrightarrow> is_conj B \<Longrightarrow> Q A2 B) \<Longrightarrow>
      (is_lit_plus A1 \<Longrightarrow> is_conj A2 \<Longrightarrow> is_conj B \<Longrightarrow> Q (A1 \<^bold>\<and> A2) B)) \<Longrightarrow>
    Q A B"
proof -
  (* can't I reference this differently? *)
  assume assm: "\<And>B. is_conj B \<Longrightarrow> Q \<bottom> B"
    "\<And>B. is_conj B \<Longrightarrow> Q (\<^bold>\<not> \<bottom>) B"
    "\<And>a B. is_conj B \<Longrightarrow> Q (Atom a) B"
    "\<And>a B. is_conj B \<Longrightarrow> Q (\<^bold>\<not> (Atom a)) B"
    "\<And>A1 A2 B.
      (is_conj A2 \<Longrightarrow> is_conj B \<Longrightarrow> Q A2 B) \<Longrightarrow>
      (is_lit_plus A1 \<Longrightarrow> is_conj A2 \<Longrightarrow> is_conj B \<Longrightarrow> Q (A1 \<^bold>\<and> A2) B)"
  have "is_conj A \<and> is_conj B \<longrightarrow> Q A B"
    apply (rule conjAnd.induct)
    using assm by simp_all
  with assms show ?thesis by simp
qed

lemma conjAnd_is_conj:
  assumes "is_conj A \<and> is_conj B" shows "is_conj (conjAnd A B)"
  by (induction A B rule: conjAnd_induct_isconj) (simp_all add: assms)
  (*by (rule conjAnd.induct[of "\<lambda>x y. is_conj x \<and> is_conj y \<longrightarrow> is_conj (conjAnd x y)"])
    simp_all*)

lemma conjAnd_sem:
  "\<A> \<Turnstile> conjAnd F G \<longleftrightarrow> \<A> \<Turnstile> F \<^bold>\<and> G"
  by (rule conjAnd.induct[of "\<lambda> F G. \<A> \<Turnstile> conjAnd F G \<longleftrightarrow> \<A> \<Turnstile> F \<^bold>\<and> G"])
    simp_all

subsection \<open> Formula Semantics \<close>

lemma entail_and: "A \<TTurnstile> a \<^bold>\<and> b \<longleftrightarrow> A \<TTurnstile> a \<and> A \<TTurnstile> b"
  by (auto simp add: entailment_def)

(* Doesn't work with OR. But this isn't a problem since closed world entailment can
   be represented as semantics of the world's valuation, and then we can apply
   \<open>BigOr_semantics\<close> *)
lemma bigAnd_entailment: "\<Gamma> \<TTurnstile> (\<^bold>\<And>F) \<longleftrightarrow>
  (\<forall>f \<in> set F. \<Gamma> \<TTurnstile> f)"
  unfolding entailment_def
  by auto

text \<open> Single formula entailment, since entailment has a formula set on the left side... \<close>

definition fmla_entailment :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> bool" ("(_ \<TTurnstile>\<^sub>1/ _)" [53,53] 53) where
  "F \<TTurnstile>\<^sub>1 G \<equiv> \<forall>\<A>. \<A> \<Turnstile> F \<longrightarrow> \<A> \<Turnstile> G"

(*lemma fmla_ent_ent: "F \<TTurnstile>\<^sub>1 G \<Longrightarrow> \<Gamma> \<TTurnstile> F \<Longrightarrow> \<Gamma> \<TTurnstile> G"
  using fmla_entailment_def entailment_def by metis*)

lemma fmla_ent_ent: "F \<TTurnstile>\<^sub>1 G \<longleftrightarrow> (\<forall>\<Gamma>. \<Gamma> \<TTurnstile> F \<longrightarrow> \<Gamma> \<TTurnstile> G)"
  apply (rule)
  using fmla_entailment_def entailment_def apply metis
  using fmla_entailment_def entailment_def apply fastforce
  done

text \<open> Other formula properties \<close>

thm atoms_BigAnd
(* this one isn't in Formulas.thy *)
lemma atoms_BigOr[simp]: "atoms (\<^bold>\<Or> \<phi>s) = \<Union>(atoms ` set \<phi>s)"
  by (induction \<phi>s) simp_all

lemma bigAnd_map: "(\<^bold>\<And>(map (map_formula f) \<phi>s)) = map_formula f (\<^bold>\<And>\<phi>s)"
  by (induction \<phi>s; simp_all)
lemma bigOr_map: "(\<^bold>\<Or>(map (map_formula f) \<phi>s)) = map_formula f (\<^bold>\<Or>\<phi>s)"
  by (induction \<phi>s; simp_all)

lemma bigAnd_map_atom: "(\<^bold>\<And>(map ((map_formula \<circ> map_atom) f) \<phi>s)) =
  (map_formula \<circ> map_atom) f (\<^bold>\<And>\<phi>s)"
  using bigAnd_map by auto
lemma bigOr_map_atom: "(\<^bold>\<Or>(map ((map_formula \<circ> map_atom) f) \<phi>s)) =
  (map_formula \<circ> map_atom) f (\<^bold>\<Or>\<phi>s)"
  using bigOr_map by auto

lemma map_formula_bigOr: "(\<^bold>\<Or> (map (map_formula f) \<phi>s)) = map_formula f (\<^bold>\<Or> \<phi>s)"
  by (induction \<phi>s; simp_all)

subsection \<open> STRIPS Formulas \<close>

text \<open>The lemma \<open>Propositional_Proof_Systems.Sema.pn_atoms_updates\<close> is in a very unfortunate form,
  so I have to split it.\<close>

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