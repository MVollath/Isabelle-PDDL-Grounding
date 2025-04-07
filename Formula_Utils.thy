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


(* assumes the argument to be in a right-deep tree, i.e. is_conj *)
(* possible optimization: un_and (Not Bot) = []" *)
(* still is defined and preserves semantics if argument isn't a pure right conjunction *)
fun un_and :: "'a formula \<Rightarrow> 'a formula list" where
  "un_and (F \<^bold>\<and> G) = F # un_and G" |
  "un_and F = [F]"

lemma "is_conj F \<Longrightarrow> \<forall>f \<in> set (un_and F). is_lit_plus f"
  by (induction F rule: is_conj.induct) simp_all

lemma un_and_sem: "A \<Turnstile> F \<longleftrightarrow> (\<forall>f \<in> set (un_and F). A \<Turnstile> f)"
  by (induction F) simp_all

fun is_lit_pos :: "'a formula \<Rightarrow> bool" where
  "is_lit_pos \<bottom> = True" |
  "is_lit_pos (Not \<bottom>) = True" |
  "is_lit_pos (Atom _) = True" |
  "is_lit_pos _ = False"

lemma lit_pos_vs_plus: "is_lit_pos l = is_lit_plus l \<or> (\<exists>a. l = \<^bold>\<not> (Atom a))"
  by (cases l rule: is_lit_plus.cases) simp_all

fun is_pos_conj :: "'a formula \<Rightarrow> bool" where
  "is_pos_conj (F \<^bold>\<and> G) \<longleftrightarrow> is_lit_pos F \<and> is_pos_conj G" |
  "is_pos_conj F \<longleftrightarrow> is_lit_pos F"

lemma pos_conj_conj: "is_pos_conj F \<Longrightarrow> is_conj F"
  apply (induction F rule: is_conj.induct) using lit_pos_vs_plus apply force
  apply simp_all using lit_pos_vs_plus by force

lemma "is_pos_conj F \<Longrightarrow> \<forall>f \<in> set (un_and F). is_lit_pos f"
  by (induction F rule: is_conj.induct) simp_all

(* This is only defined for pure conjunctive clauses. *)
(* TODO maybe extend the definition for other use cases? *)

fun relax_lit :: "'a formula \<Rightarrow> 'a formula" where
  "relax_lit \<bottom> = \<^bold>\<not> \<bottom>" |
  "relax_lit (\<^bold>\<not> \<bottom>) = \<^bold>\<not> \<bottom>" |
  "relax_lit (Atom a) = Atom a" |
  "relax_lit (\<^bold>\<not> (Atom a)) = \<^bold>\<not> \<bottom>"

lemma relax_lit_pos: "is_lit_plus f \<Longrightarrow> is_lit_pos (relax_lit f)"
  by (cases f rule: relax_lit.cases) simp_all

(* also only defined for is_conj *)
fun relax_conj :: "'a formula \<Rightarrow> 'a formula" where
  "relax_conj (F \<^bold>\<and> G) = relax_lit F \<^bold>\<and> relax_conj G" |
  "relax_conj f = relax_lit f"

lemma relax_conj_pos: "is_conj F \<Longrightarrow> is_pos_conj (relax_conj F)"
  apply (induction F rule: is_conj.induct) apply (simp_all add: relax_lit_pos)
  subgoal for v apply (cases v) apply simp_all done done

(* can probably think of a stronger property *)
lemma relax_conj_un_conj:
  assumes "is_conj F"
  shows "set (un_and (relax_conj F)) \<subseteq> \<^bold>\<not>\<bottom> \<triangleright> set (un_and F)"
  using assms proof (induction F rule: is_conj.induct)
  case (1 F G) thus ?case
    apply (cases F) apply auto[6] subgoal for x by (cases x) simp_all
    done
next
  case ("2_3" v)
  then show ?case by (cases v) simp_all
qed simp_all

lemma relax_conj_sem:
  assumes "is_conj F"
  shows "A \<Turnstile> F \<Longrightarrow> A \<Turnstile> relax_conj F"
proof -
  have "A \<Turnstile> relax_conj F \<longleftrightarrow> (\<forall>l \<in> set (un_and (relax_conj F)). A \<Turnstile> l)"
    using un_and_sem by blast
  hence "(\<forall>l \<in> \<^bold>\<not>\<bottom> \<triangleright> set (un_and F). A \<Turnstile> l) \<Longrightarrow> A \<Turnstile> relax_conj F"
    using assms using relax_conj_un_conj by blast
  thus "A \<Turnstile> F \<Longrightarrow> A \<Turnstile> relax_conj F" using un_and_sem by auto
qed


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