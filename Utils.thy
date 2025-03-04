theory Utils
  imports
    "Propositional_Proof_Systems.Sema"
    "Propositional_Proof_Systems.CNF_Formulas"
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
begin

(* for testing *)
definition
  "showvals f xs \<equiv> map (\<lambda>x. (x, f x)) xs"

fun showsteps :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list" where
  "showsteps f i [] = [i]" |
  "showsteps f i (x # xs) = i # showsteps f (f i x) xs"

(* syntax sugar *)


text \<open> Not using the default list_all because it makes proofs cumbersome \<close>
abbreviation (input) list_all1 where
  "list_all1 P xs \<equiv> \<forall>x \<in> set xs. P x"

(* lists *)

fun sublist_until :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "sublist_until [] a = []" |
  "sublist_until (x # xs) a =
    (if x = a then [] else x # sublist_until xs a)"


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

(* formula helpers *)
(* consider right deep prop (A&B) \<longleftrightarrow> literal A & prop B *)

fun only_conj :: "'a formula \<Rightarrow> bool" where
  "only_conj (Atom a) \<longleftrightarrow> True" | (* literal *)
  "only_conj (\<^bold>\<not> (Atom a)) \<longleftrightarrow> True" | (* literal *)
  "only_conj \<bottom> \<longleftrightarrow> True" | (* literal *)
  "only_conj (\<^bold>\<not>\<bottom>) \<longleftrightarrow> True" | (* literal *)

  "only_conj (\<phi> \<^bold>\<and> \<psi>) \<longleftrightarrow> only_conj \<phi> \<and> only_conj \<psi>" | (* conjunct *)

  "only_conj (\<^bold>\<not> _) \<longleftrightarrow> False" |
  "only_conj (_ \<^bold>\<or> _) \<longleftrightarrow> False" |
  "only_conj (_ \<^bold>\<rightarrow> _) \<longleftrightarrow> False"

fun in_dnf :: "'a formula \<Rightarrow> bool" where
  "in_dnf (Atom a) \<longleftrightarrow> True" | (* literal *)
  "in_dnf (\<^bold>\<not> (Atom a)) \<longleftrightarrow> True" | (* literal *)
  "in_dnf \<bottom> \<longleftrightarrow> True" | (* literal *)
  "in_dnf (\<^bold>\<not>\<bottom>) \<longleftrightarrow> True" | (* literal *)

  "in_dnf (\<phi> \<^bold>\<or> \<psi>) \<longleftrightarrow> in_dnf \<phi> \<and> in_dnf \<psi>" | (* disjunct *)
  "in_dnf (\<phi> \<^bold>\<and> \<psi>) \<longleftrightarrow> only_conj \<phi> \<and> only_conj \<psi>" | (* conjunct *)

  "in_dnf (\<^bold>\<not> _) \<longleftrightarrow> False" |
  "in_dnf (_ \<^bold>\<rightarrow> _) \<longleftrightarrow> False"
  

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

lemma map_set_comprehension:
  "{f (xs ! i) | i. i < length xs} = set (map f xs)"
proof -
  have "{f (xs ! i) | i. i < length xs} = {f x | x. x \<in> set xs}"
    by (metis in_set_conv_nth)
  thus ?thesis by auto
qed

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

lemma bigAnd_atoms: "atoms (\<^bold>\<And> \<phi>s) = \<Union>(atoms ` set \<phi>s)"
  by (induction \<phi>s) simp_all

lemma bigOr_atoms: "atoms (\<^bold>\<Or> \<phi>s) = \<Union>(atoms ` set \<phi>s)"
  by (induction \<phi>s) simp_all


subsection \<open> Formula Preds \<close>

fun fmla_preds :: "'ent atom formula \<Rightarrow> predicate set" where
  "fmla_preds (Atom (predAtm p xs)) = {p}" |
  "fmla_preds (Atom (Eq a b)) = {}" |
  "fmla_preds \<bottom> = {}" |
  "fmla_preds (\<^bold>\<not> \<phi>) = fmla_preds \<phi>" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<rightarrow> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2"

lemma fmla_preds_alt: "fmla_preds \<phi> = {p | p xs. predAtm p xs \<in> atoms \<phi>}"
  apply (induction \<phi>)
  subgoal for x
    apply (cases x; simp_all)
    done
  by auto


lemma map_preserves_fmla_preds: "fmla_preds F = fmla_preds ((map_formula \<circ> map_atom) f F)"
proof (induction F)
  case (Atom x)
  thus ?case by (cases x) simp_all
qed auto

lemma notin_fmla_preds_notin_atoms: "p \<notin> fmla_preds \<phi> \<Longrightarrow> predAtm p args \<notin> atoms \<phi>"
  using fmla_preds_alt by blast

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