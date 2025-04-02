theory Utils
  imports
    "Propositional_Proof_Systems.Sema"
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

(* proof rules *)

lemma eq_contr: "(a = b \<Longrightarrow> False) \<Longrightarrow> a \<noteq> b"
  by auto

(* lists *)

fun sublist_until :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "sublist_until [] a = []" |
  "sublist_until (x # xs) a =
    (if x = a then [] else x # sublist_until xs a)"

lemma sublist_just_until:
  assumes "x \<in> set xs"
  shows "\<exists>ys. sublist_until xs x @ [x] @ ys = xs"
  using assms by (induction xs) auto

lemma notin_sublist_until:
  "x \<notin> set (sublist_until xs x)"
  by (induction xs) simp_all

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

lemma append_r_distinct: "distinct xs \<Longrightarrow> distinct (map (\<lambda>x. x @ p) xs)" (is "?L \<Longrightarrow> ?R")
proof - (* TODO how to apply contradiction correctly here? *)
  assume l: ?L
  {assume "\<not>?R"
    then obtain i j where
      ij: "i < length xs" "j < length xs" "i \<noteq> j"
      "map (\<lambda>x. x @ p) xs ! i = map (\<lambda>x. x @ p) xs ! j"
      by (metis distinct_conv_nth length_map)
    hence "xs ! i = xs ! j" by simp
    hence "\<not>?L" using ij distinct_conv_nth by blast}
  thus ?thesis using l by auto
qed

lemma append_l_distinct: "distinct xs \<Longrightarrow> distinct (map ((@)p) xs)" (is "?L \<Longrightarrow> ?R")
proof - (* TODO how to apply contradiction correctly here? *)
  assume l: ?L
  {assume "\<not>?R"
    then obtain i j where
      ij: "i < length xs" "j < length xs" "i \<noteq> j"
      "map ((@)p) xs ! i = map ((@)p) xs ! j"
      by (metis distinct_conv_nth length_map)
    hence "xs ! i = xs ! j" by simp    
    hence "\<not>?L" using ij distinct_conv_nth by blast}
  thus ?thesis using l by auto
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