theory PDDL_to_STRIPS
  imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    "AI_Planning_Languages_Semantics.Option_Monad_Add"
    "Verified_SAT_Based_AI_Planning.STRIPS_Semantics"
    PDDL_Sema_Supplement Normalization_Definitions
    Utils Formula_Utils (* String_Shenanigans *)
    "Propositional_Proof_Systems.CNF"
    (* list linorder: *) "HOL-Library.List_Lexorder" "HOL-Library.Char_ord" (* only used to minimize negative variables *)
begin

term "sorted_list_of_set :: string set \<Rightarrow> string list"

text \<open>There are two big differences between normalized ground PDDL and
  STRIPS. Normalized PDDL formulas are pure conjunctions, but they can contain
  \<bottom> and negative atoms. These differences require workarounds:
- We introduce negative variants of all ground predicates in the STRIPS task.
  Init and operator effects are modified accordingly.
  TODO: only use negative variables where needed, i.e.: when the goal clause or
  operator preconditions contain the negative literal.
- A new static variable that is always false is introduced to be used in place of \<bottom>.
  Although technically not needed since it can always be removed from clauses,
  we also introduce a static variable for \<not>\<bottom>.
- Of course, we could also omit any operators whose preconditions contain \<bottom>, but this
  seemed easier.
\<close>

(* converting conj into a clause as list *)
(* assumes is_conj. TODO Utils *)
fun as_clause :: "'a formula \<Rightarrow> 'a formula list" where
  "as_clause (A \<^bold>\<and> B) = A # as_clause B" |
  "as_clause A = [A]"

definition "v\<^sub>T \<equiv> ''+'' :: name"
definition "v\<^sub>F \<equiv> ''-'' :: name"
abbreviation "vpos p \<equiv> CHR ''+'' # predicate.name p"
abbreviation "vneg p \<equiv> CHR ''-'' # predicate.name p"
lemmas vb_defs = v\<^sub>T_def v\<^sub>F_def

fun pred_vpos :: "predicate_decl \<Rightarrow> name" where
  "pred_vpos (PredDecl n args) = vpos n"
fun pred_vneg :: "predicate_decl \<Rightarrow> name" where
  "pred_vneg (PredDecl n args) = vneg n"

(* Converting formulas into variables *)
(* assumes is_lit_plus and not Eq *)
fun lit_as_var :: "'a atom formula \<Rightarrow> name" where
  "lit_as_var \<bottom> = v\<^sub>F" |
  "lit_as_var (\<^bold>\<not>\<bottom>) = v\<^sub>T" |
  "lit_as_var (Atom (predAtm n args)) = vpos n" |
  "lit_as_var (\<^bold>\<not>(Atom (predAtm n args))) = vneg n"

definition fmla_as_vars :: "'a atom formula \<Rightarrow> name list" where
  "fmla_as_vars F \<equiv> map lit_as_var (as_clause F)"

fun lit_as_goal :: "'a atom formula \<Rightarrow> (name \<times> bool)" where
  "lit_as_goal \<bottom> = (v\<^sub>F, True)" |
  "lit_as_goal (\<^bold>\<not>\<bottom>) = (v\<^sub>T, True)" | (* equivalent: (v\<^sub>F, False) *)
  "lit_as_goal (Atom (predAtm n args)) = (vpos n, True)" |
  "lit_as_goal (\<^bold>\<not>(Atom (predAtm n args))) = (vpos n, False)"

abbreviation "fmla_as_goals F \<equiv> map lit_as_goal (as_clause F)"

(* atm_as_vpos is technically subsumed by lit_as_var *)
fun atm_as_vpos :: "'a atom formula \<Rightarrow> name" where
  "atm_as_vpos (Atom (predAtm n args)) = vpos n"
fun atm_as_vneg :: "'a atom formula \<Rightarrow> name" where
  "atm_as_vneg (Atom (predAtm n args)) = vneg n"

(* add effects take precedence *)
(* removes duplicates *)
fun fix_effect :: "'a ast_effect \<Rightarrow> 'a ast_effect" where
  "fix_effect (Effect add del) = Effect add (filter (\<lambda>x. x \<notin> set add) del)"

fun as_strips_op :: "ast_action_schema \<Rightarrow> name strips_operator" where
  "as_strips_op (Action_Schema n args pre eff) =
  (let eff' = fix_effect eff; add = adds eff'; del = dels eff' in
  \<lparr>
    precondition_of = fmla_as_vars pre
    , add_effects_of = map atm_as_vpos add @ map atm_as_vneg del
    , delete_effects_of = map atm_as_vpos del @ map atm_as_vneg add \<rparr>)"

context ast_problem begin

definition "pos_vars = v\<^sub>T # map pred_vpos (predicates D)"
definition "neg_vars = v\<^sub>F # map pred_vneg (predicates D)"
abbreviation "strips_vars \<equiv> pos_vars @ neg_vars"
lemmas vars_defs = pos_vars_def neg_vars_def
(*
  initD: ["A", "B"]
  pvars: + A B C,
  nvars: - a b c,
  "init": [+, A, B]
  empty: +:0, A:0, B:0, C:0, -:1, a:1, b:1, c:1
  init: +:1, A:1, B:1, C:0, -:0, a:0, b:0, c:1
*)

abbreviation "pos_empty \<equiv> fold (\<lambda>v s. s(v \<mapsto> False)) pos_vars (\<lambda>x. None)"
definition "empty_state \<equiv> fold (\<lambda>v s. s(v \<mapsto> True)) neg_vars pos_empty"
definition (in -) "upd_init a s \<equiv> s(atm_as_vpos a \<mapsto> True, atm_as_vneg a \<mapsto> False)"
definition strips_init :: "name strips_state" where
  "strips_init \<equiv> fold upd_init (init P) empty_state"
lemmas init_defs = empty_state_def upd_init_def strips_init_def

fun (in -) upd_goal where "upd_goal (v, b) s = s(v \<mapsto> b)"
definition strips_goal :: "name strips_state" where
  "strips_goal \<equiv> fold upd_goal (fmla_as_goals (goal P)) (\<lambda>x. None)"

definition as_strips :: "name strips_problem" where
  "as_strips \<equiv> \<lparr> 
    variables_of = strips_vars
    , operators_of = map as_strips_op (actions D)
    , initial_of = strips_init
    , goal_of = strips_goal \<rparr>"

definition "restore_pddl_pa op_i \<equiv> PAction (ac_name (actions D ! op_i)) []"
definition "restore_pddl_plan op_is \<equiv> map restore_pddl_pa op_is"

end

lemmas to_strips_code =
  ast_problem.vars_defs
  ast_problem.init_defs
  ast_problem.strips_goal_def
  ast_problem.as_strips_def
  ast_problem.restore_pddl_pa_def
  ast_problem.restore_pddl_plan_def
declare to_strips_code[code]

value "ast_problem.as_strips" (* checking if code exists *)

subsection \<open> Alternative definitions \<close>

context ast_problem begin

lemma as_strips_op_sel:
  fixes ac
  defines "eff' \<equiv> fix_effect (ac_eff ac)"
  shows "precondition_of (as_strips_op ac) = fmla_as_vars (ac_pre ac)"
  "add_effects_of (as_strips_op ac) = map atm_as_vpos (adds eff') @ map atm_as_vneg (dels eff')"
  "delete_effects_of (as_strips_op ac) = map atm_as_vpos (dels eff') @ map atm_as_vneg (adds eff')"
  apply (cases ac) apply simp_all unfolding as_strips_op.simps Let_def apply simp
  apply (cases ac) apply simp_all unfolding as_strips_op.simps Let_def eff'_def apply simp
  apply (cases ac) apply simp_all unfolding as_strips_op.simps Let_def eff'_def by simp

lemma as_strips_sel:
  "as_strips \<^sub>\<V> = strips_vars"
  "as_strips \<^sub>\<O> = map as_strips_op (actions D)"
  "as_strips \<^sub>I = strips_init"
  "as_strips \<^sub>G = strips_goal"
  unfolding as_strips_def by simp_all
end

subsection \<open> Formula proofs \<close>

(* TODO Utils *)
lemma as_clause_sem: "A \<Turnstile> F \<longleftrightarrow> (\<forall>a \<in> set (as_clause F). A \<Turnstile> a)"
  by (induction F) simp_all
(* ? *)
lemma as_clause_lits: assumes "is_conj F" shows "list_all1 is_lit_plus (as_clause F)"
  using assms by (induction F rule: is_conj.induct) simp_all

(* as_clause structure *)
abbreviation (input) "no_eqs F \<equiv> \<forall>a b. Eq a b \<notin> atoms F"
fun is_predatm_lit where
  "is_predatm_lit \<bottom> = True" |
  "is_predatm_lit (\<^bold>\<not>\<bottom>) = True" |
  "is_predatm_lit (Atom (predAtm n args)) = True" |
  "is_predatm_lit (\<^bold>\<not>(Atom (predAtm n args))) = True" |
  "is_predatm_lit _ = False"
(* ? *)
lemma is_predatm_lit_plus: "is_predatm_lit F \<Longrightarrow> is_lit_plus F"
  by (cases F rule: is_predatm_lit.cases) simp_all
lemma no_eqs_as_clause:
  assumes "is_conj F \<and> no_eqs F"
  shows "list_all1 is_predatm_lit (as_clause F)"
using assms proof (induction F rule: as_clause.induct)
  case (1 A B)
  thus ?case by (cases A rule: is_predatm_lit.cases) force+
next
  case ("2_1" a)
  thus ?case by (cases a) simp_all
next
  case ("2_3" a)
  thus ?case by (cases a rule: is_predAtom.cases) simp_all
qed simp_all

(* grounded no eq *)

context wf_grounded_problem begin

lemma objT_empty: "objT = (\<lambda>x. None)"
  using grounded_prob grounded_dom
  unfolding grounded_prob_def grounded_dom_def objT_def constT_def by auto

lemma (in wf_ast_domain) wf_empty_atoms:
  assumes "wf_fmla (\<lambda>x. None) F"
  shows 
    "\<forall>a \<in> atoms F. \<exists>n. a = predAtm n [] \<and> PredDecl n [] \<in> set (predicates D)"
using assms proof (induction F)
  case (Atom x)
  then show ?case proof (cases x)
    case (predAtm n args)
    with Atom obtain Ts where 1: "sig n = Some Ts" "list_all2 (is_of_type (\<lambda>x. None)) args Ts"
      unfolding predAtm wf_fmla.simps wf_atom.simps wf_pred_atom.simps
      using case_optionE by blast
    hence 2: "args = [] \<and> Ts = []" unfolding is_of_type_def
      using list.rel_cases by auto
    with 1 have "PredDecl n [] \<in> set (predicates D)"
      using sig_Some by blast
    with 2 show ?thesis using predAtm by simp
  qed simp
qed auto

lemma (in wf_ast_domain) wf_empty_no_eqs:
  assumes "wf_fmla (\<lambda>x. None) F"
  shows "Eq a b \<notin> atoms F"
  using assms wf_empty_atoms by blast

lemma goal_no_eqs: "Eq a b \<notin> atoms (goal P)"
  using objT_empty wf_P(5) wf_empty_no_eqs by simp

context fixes ac assumes ac_in: "ac \<in> set (actions D)" begin

lemma ac_tyt_empty: "ac_tyt ac = (\<lambda>x. None)"
proof -
  have 1: "constT = (\<lambda>x. None)" using grounded_dom grounded_dom_def constT_def by simp
  from ac_in have "grounded_ac ac" using grounded_dom grounded_dom_def by blast
  hence 2: "ac_params ac = []" by (cases ac) simp
  thus "?thesis"
    apply (intro ext)
    subgoal for x
      using 1 2 by (cases x) simp_all
    done
qed

lemma pre_no_eqs: "Eq a b \<notin> atoms (ac_pre ac)"
  using ac_in ac_tyt_empty
  using wf_D(7) wf_action_schema_alt wf_empty_no_eqs  by metis

lemma ac_pre_atoms:
  "\<forall>a \<in> atoms (ac_pre ac). \<exists>n. a = predAtm n [] \<and> PredDecl n [] \<in> set (predicates D)"
  using ac_in ac_tyt_empty
  using wf_D(7) wf_action_schema_alt wf_empty_atoms by metis

lemma ac_eff_empty:
  "list_all1 (wf_fmla_atom (\<lambda>x. None)) (adds (ac_eff ac))"
  "list_all1 (wf_fmla_atom (\<lambda>x. None)) (dels (ac_eff ac))"
  using ac_in ac_tyt_empty
  using wf_D(7) wf_action_schema_alt wf_effect_alt by metis+

end

(* not needed for init and effs, since it direcly follows with wf_fmla_atom_alt *)
end

subsection \<open> STRIPS task is WF \<close>

context wf_normed_grounded_problem begin

thm ListMem_iff

thm wf_fmla_alt

lemma a: "PredDecl n [] \<in> set (predicates D) \<Longrightarrow> vpos n \<in> pred_vpos ` set (predicates D)"
  by force
lemma b: "PredDecl n [] \<in> set (predicates D) \<Longrightarrow> vneg n \<in> pred_vneg ` set (predicates D)"
  by force


lemma fmla_vars_covered:
  assumes "is_conj F" "\<forall>a \<in> atoms F. \<exists>n. a = predAtm n [] \<and> PredDecl n [] \<in> set (predicates D)"
  shows "set (fmla_as_vars F) \<subseteq> set strips_vars"
  unfolding fmla_as_vars_def vars_defs
  using assms apply (induction F rule: as_clause.induct)
  subgoal for A apply (cases A rule: lit_as_var.cases)
    apply simp_all
    using a b by fast+
  subgoal for v by (cases v) force+
  apply simp_all
  subgoal for v by (cases v rule: is_predAtom.cases) force+
  done

thm wf_empty_atoms

lemma wf_empty_fmla_atom:
  assumes "wf_fmla_atom (\<lambda>x. None) a"
  shows "\<exists>n. a = Atom (predAtm n []) \<and> PredDecl n [] \<in> set (predicates D)"
  using assms wf_empty_atoms
  unfolding wf_fmla_atom_alt
  apply (cases a rule: is_predAtom.cases) by fastforce+

lemma wf_empty_atom_covered:
  assumes "wf_fmla_atom (\<lambda>x. None) a"
  shows "atm_as_vpos a \<in> set strips_vars" "atm_as_vneg a \<in> set strips_vars"
  unfolding vars_defs
  using assms[THEN wf_empty_fmla_atom] apply (cases a rule: is_predAtom.cases) apply force+
  using assms[THEN wf_empty_fmla_atom] apply (cases a rule: is_predAtom.cases) by force+

find_theorems "set (map ?f ?xs) = ?f ` set ?xs"

abbreviation "empty_atom a \<equiv> \<exists>n. a = Atom (predAtm n []) \<and> PredDecl n [] \<in> set (predicates D)"

lemma wf_as_strips_op:
  assumes "ac \<in> set (actions D)"
  shows "is_valid_operator_strips as_strips (as_strips_op ac)"
  unfolding is_valid_operator_strips_def Let_def ListMem_iff Ball_set[symmetric]
  unfolding as_strips_sel
  apply (intro conjI)
  unfolding as_strips_op_sel
proof -
  from assms have "no_eqs (ac_pre ac)" using pre_no_eqs by blast
  note 1 = ac_pre_atoms[OF assms]
  from assms have "is_conj (ac_pre ac)"
    using normed_dom unfolding prec_normed_dom_def by fast

  from fmla_vars_covered[OF this 1] show "\<forall>v\<in>set (fmla_as_vars (ac_pre ac)). v \<in> set strips_vars"
    by blast

  obtain a d where eff: "ac_eff ac = Effect a d" by (cases "ac_eff ac") simp

  have 1: "\<forall>v \<in> atm_as_vpos ` set a. v \<in> set strips_vars"
          "\<forall>v \<in> atm_as_vneg ` set a. v \<in> set strips_vars"
          "\<forall>v \<in> atm_as_vpos ` set d. v \<in> set strips_vars"
          "\<forall>v \<in> atm_as_vneg ` set d. v \<in> set strips_vars"
    using eff wf_empty_atom_covered ac_eff_empty[OF assms] by auto

  thus "\<forall>v\<in>set (map atm_as_vpos (adds (fix_effect (ac_eff ac))) @
             map atm_as_vneg (dels (fix_effect (ac_eff ac)))).
       v \<in> set strips_vars" unfolding eff by auto

  from 1 show "\<forall>v\<in>set (map atm_as_vpos (dels (fix_effect (ac_eff ac))) @
             map atm_as_vneg (adds (fix_effect (ac_eff ac)))).
       v \<in> set strips_vars" unfolding eff by auto

  let ?adds = "adds (fix_effect (ac_eff ac))"
  let ?dels = "dels (fix_effect (ac_eff ac))"

  note ac_eff_empty[OF assms] wf_empty_fmla_atom
  hence eatms: "list_all1 empty_atom ?adds \<and> list_all1 empty_atom ?dels"
    by (cases "ac_eff ac") auto
  have v_inj: "x \<noteq> y \<Longrightarrow> empty_atom x \<Longrightarrow> empty_atom y \<Longrightarrow>
    atm_as_vpos x \<noteq> atm_as_vpos y \<and> atm_as_vneg x \<noteq> atm_as_vneg y" for x y
    apply (cases x rule: is_predAtom.cases; cases y rule: is_predAtom.cases; simp)
    subgoal for u v apply (cases u; cases v) by simp done
  have p_neq_n: "empty_atom x \<Longrightarrow> atm_as_vpos x \<noteq> atm_as_vneg x" for x
    by (cases x rule: is_predAtom.cases) simp_all

  have 0: "set ?adds \<inter> set ?dels = {}"
    by (cases "ac_eff ac") auto
  have 1: "atm_as_vpos ` set ?adds \<inter> atm_as_vpos ` set ?dels = {}"
  proof -
    have "\<forall>x \<in> set ?adds. \<forall>y \<in> set ?dels. x \<noteq> y" using 0 by blast
    hence "\<forall>x \<in> set ?adds. \<forall>y \<in> set ?dels. atm_as_vpos x \<noteq> atm_as_vpos y"
      using eatms v_inj by metis
    thus ?thesis by blast
  qed
  have 2: "atm_as_vneg ` set ?adds \<inter> atm_as_vneg ` set ?dels = {}"
  proof -
    have "\<forall>x \<in> set ?adds. \<forall>y \<in> set ?dels. x \<noteq> y" using 0 by blast
    hence "\<forall>x \<in> set ?adds. \<forall>y \<in> set ?dels. atm_as_vneg x \<noteq> atm_as_vneg y"
      using eatms v_inj by metis
    thus ?thesis by blast
  qed
  have 3:
    "atm_as_vpos ` set ?adds \<inter> atm_as_vneg ` set ?adds = {}"
  proof -
    {
      fix x y assume a: "x \<in> set ?adds" "y \<in> set ?adds"
      hence "empty_atom x" "empty_atom y" by (simp_all add: eatms)
      hence "atm_as_vneg x \<noteq> atm_as_vpos y"
        using eatms by (cases x rule: is_predAtom.cases; cases y rule: is_predAtom.cases)
        simp_all
    }
    thus ?thesis by force
  qed
  have 4: "atm_as_vpos ` set ?dels \<inter> atm_as_vneg ` set ?dels = {}"
  proof -
    {
      fix x y assume a: "x \<in> set ?dels" "y \<in> set ?dels"
      hence "empty_atom x" "empty_atom y" by (simp_all add: eatms)
      hence "atm_as_vneg x \<noteq> atm_as_vpos y"
        using eatms by (cases x rule: is_predAtom.cases; cases y rule: is_predAtom.cases)
        simp_all
    }
    thus ?thesis by force
  qed

  show "\<forall>v\<in>set (map atm_as_vpos (adds (fix_effect (ac_eff ac))) @
             map atm_as_vneg (dels (fix_effect (ac_eff ac)))).
       v \<notin> set (map atm_as_vpos (dels (fix_effect (ac_eff ac))) @
                 map atm_as_vneg (adds (fix_effect (ac_eff ac))))"
    apply simp
    using 1 2 3 4
    by (metis Set.set_insert Un_iff insert_disjoint(1))

  show "\<forall>v\<in>set (map atm_as_vpos (dels (fix_effect (ac_eff ac))) @
             map atm_as_vneg (adds (fix_effect (ac_eff ac)))).
       v \<notin> set (map atm_as_vpos (adds (fix_effect (ac_eff ac))) @
                 map atm_as_vneg (dels (fix_effect (ac_eff ac))))"
    apply simp
    using 1 2 3 4
    by (metis Set.set_insert Un_iff insert_disjoint(1))
qed

theorem init_covered: "strips_init v \<noteq> None \<longleftrightarrow> v \<in> set strips_vars"
proof -
  have i: "fold (\<lambda>v s. s(v \<mapsto> b)) vars s v \<noteq> None \<longleftrightarrow> v \<in> set vars \<or> s v \<noteq> None"
    for b vars s by (induction vars arbitrary: s) simp_all
  from i have "empty_state v \<noteq> None \<longleftrightarrow> v \<in> set neg_vars \<or> v \<in> set pos_vars"
    unfolding empty_state_def using i by metis
  hence k: "empty_state v \<noteq> None \<longleftrightarrow> v \<in> set strips_vars" by force

  have j: "fold upd_init vars s v \<noteq> None \<longleftrightarrow> s v \<noteq> None \<or>
    (\<exists>x \<in> set vars. atm_as_vpos x = v \<or> atm_as_vneg x = v)" for vars s
    unfolding upd_init_def by (induction vars arbitrary: s) auto
  moreover have "\<exists>x \<in> set (init P). atm_as_vpos x = v \<or> atm_as_vneg x = v \<Longrightarrow> v \<in> set strips_vars"
    using wf_P(4) unfolding wf_world_model_def objT_empty
    using wf_empty_atom_covered by blast
  ultimately show ?thesis unfolding strips_init_def using k by blast
qed



theorem goal_covered:
  assumes "strips_goal v \<noteq> None"
  shows "ListMem v strips_vars"
  sorry

theorem wf_as_strips: "is_valid_problem_strips as_strips"
  unfolding is_valid_problem_strips_def Let_def as_strips_sel
  apply (intro conjI)
  using wf_as_strips_op unfolding Ball_set[symmetric] apply simp
  using init_covered apply (meson ListMem_iff)
  using goal_covered by (meson ListMem_iff)



end

end