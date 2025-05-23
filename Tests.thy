theory Tests
  imports Main
    (*"../LTS-formalization/Datalog/Datalog"*)
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    "Show.Show" DNF
    (*"AI_Planning_Languages_Semantics.PDDL_STRIPS_Checker" *)
begin






section \<open> rightAnd \<close>
(* unused after all in grounding pipeline *)
(* Like formula.And but it preserves the conjunct being a right-deep tree. *)
fun rightAnd :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> 'a formula" (infix "\<^bold>\<and>\<^sub>R" 68) where
  "\<bottom> \<^bold>\<and>\<^sub>R B = \<bottom> \<^bold>\<and> B" |
  "(\<^bold>\<not> \<bottom>) \<^bold>\<and>\<^sub>R B = (\<^bold>\<not> \<bottom>) \<^bold>\<and> B" |
  "(Atom a) \<^bold>\<and>\<^sub>R B = (Atom a) \<^bold>\<and> B" |
  "(\<^bold>\<not> (Atom a)) \<^bold>\<and>\<^sub>R B = (\<^bold>\<not> (Atom a)) \<^bold>\<and> B" |
  "(A1 \<^bold>\<and> A2) \<^bold>\<and>\<^sub>R B = A1 \<^bold>\<and> (A2 \<^bold>\<and>\<^sub>R B)" |
  "A \<^bold>\<and>\<^sub>R B = A \<^bold>\<and> B"

text \<open> I struggle to correctly apply (induction ... rule: rightAnd.induct), so the following lemma
  helps to simplify it:\<close>
thm rightAnd.induct[of "\<lambda>x y. is_conj x \<and> is_conj y \<longrightarrow> Q x y"]
lemma rightAnd_induct_isconj:
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
    apply (rule rightAnd.induct)
    using assm by simp_all
  with assms show ?thesis by simp
qed

lemma rightAnd_is_conj:
  assumes "is_conj A \<and> is_conj B" shows "is_conj (A \<^bold>\<and>\<^sub>R B)"
  by (induction A B rule: rightAnd_induct_isconj) (simp_all add: assms)
  (*by (rule rightAnd.induct[of "\<lambda>x y. is_conj x \<and> is_conj y \<longrightarrow> is_conj (x \<^bold>\<and>\<^sub>R y)"])
    simp_all*)

lemma rightAnd_sem:
  "\<A> \<Turnstile> F \<^bold>\<and>\<^sub>R G \<longleftrightarrow> \<A> \<Turnstile> F \<^bold>\<and> G"
  by (rule rightAnd.induct[of "\<lambda> F G. \<A> \<Turnstile> F \<^bold>\<and>\<^sub>R G \<longleftrightarrow> \<A> \<Turnstile> F \<^bold>\<and> G"])
    simp_all

lemma rightAnd_map: "map_formula m (F \<^bold>\<and>\<^sub>R G) = map_formula m F \<^bold>\<and>\<^sub>R map_formula m G"
  by (induction F G rule: rightAnd.induct) simp_all

lemma rightAnd_atoms: "atoms (F \<^bold>\<and>\<^sub>R G) = atoms F \<union> atoms G"
  by (induction rule: rightAnd.induct) auto

lemma rightAnd_entailment: "\<Gamma> \<TTurnstile> F \<^bold>\<and>\<^sub>R G \<longleftrightarrow> \<Gamma> \<TTurnstile> F \<^bold>\<and> G"
  using entailment_def rightAnd_sem by metis


section \<open> How to prove termination \<close>

fun collatz_run :: "nat \<Rightarrow> nat" where
  "collatz_run n = undefined"
abbreviation "collatz_meaz \<equiv> measure (\<lambda>(n, i). collatz_run n)"

function (sequential) collatz :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "collatz 0 i = i" |
  "collatz (Suc 0) i = i" |
  "collatz n i = (if n mod 2 = 0 then collatz (n div 2) (Suc i) else
    collatz (3 * n + 1) (Suc i))"
by pat_completeness auto
termination proof
  show "wf collatz_meaz" by simp
next
  fix n i assume "Suc (Suc n) mod 2 = 0"
  hence "collatz_run (Suc (Suc n) div 2) < collatz_run (Suc (Suc n))" sorry
  thus "((Suc (Suc n) div 2, Suc i), (Suc (Suc n), i)) \<in> collatz_meaz"
    unfolding in_measure by simp
next
  fix n i assume "Suc (Suc n) mod 2 \<noteq> 0"
  hence "collatz_run (3 * Suc (Suc n) + 1) < collatz_run (Suc (Suc n))" sorry
  thus "((3 * Suc (Suc n) + 1, Suc i), (Suc (Suc n), i))
       \<in> collatz_meaz" by simp
qed

end