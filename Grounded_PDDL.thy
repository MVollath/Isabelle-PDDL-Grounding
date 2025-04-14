theory Grounded_PDDL
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    PDDL_Sema_Supplement Normalization_Definitions
    Utils String_Shenanigans
begin

type_synonym facty = "object atom formula" (* maybe fact_atom? *)


(* TODO split into wf_dom_grounder, dom_grounder, prob_grounder? *)

(* parameters for grounding: lists of achievable facts and applicable plan actions *)

(*fun fact_to_atom :: "fact \<Rightarrow> object atom formula" where
  "fact_to_atom (p, args) = Atom (predAtm p args)"

fun atom_to_fact :: "object atom formula \<Rightarrow> fact" where
  "atom_to_fact (Atom (predAtm p args)) = (p, args)" |
  "atom_to_fact \<phi> = undefined"*)

fun arg_str :: "object list \<Rightarrow> string" where
  "arg_str [] = ''''" |
  "arg_str [Obj n] = n" |
  "arg_str (Obj n # objs) = n @ ((CHR ''-'') # arg_str objs)"

fun fact_str :: "object atom \<Rightarrow> string" where
  "fact_str (predAtm (Pred n) args) = n @ ((CHR ''-'' # arg_str args))" |
  "fact_str _ = undefined"

fun ac_str :: "plan_action \<Rightarrow> string" where
  "ac_str (PAction n args) = n @ (CHR ''-'' # arg_str args)"

locale grounder = ast_problem +
  fixes facts :: "facty list" and ops :: "plan_action list"
begin

definition "fact_ids \<equiv> nat_range (length facts)"
definition "fact_prefix_pad \<equiv> length (show (length facts))" (* length facts - 1 is enough *)
definition "op_ids \<equiv> nat_range (length ops)"
definition "op_prefix_pad \<equiv> length (show (length ops))" (* length ops - 1 is enough *)

fun ground_pred :: "facty \<Rightarrow> nat \<Rightarrow> predicate" where
  "ground_pred (Atom a) i = Pred (padl fact_prefix_pad (show i) @ (CHR ''/'' # fact_str a))" |
  "ground_pred _ _ = undefined"

abbreviation "gr_pred_ids \<equiv> map2 ground_pred facts fact_ids"
definition "fact_map \<equiv> map_of (zip (map un_Atom facts) gr_pred_ids)"

fun map_fact :: "object atom \<Rightarrow> 'a atom" where
  "map_fact a = predAtm (the (fact_map a)) []"

(* fun grounded_pred_decl :: "facty \<Rightarrow> nat \<Rightarrow> predicate_decl" where
  "grounded_pred_decl f i = PredDecl (grounded_pred f i) []" *)

fun ga_pre :: "ground_action \<Rightarrow> term atom formula" where
  "ga_pre (Ground_Action pre eff) = map_formula map_fact pre"

fun ga_eff :: "ground_action \<Rightarrow> term ast_effect" where
  "ga_eff (Ground_Action pre (Effect a d)) =
    Effect (map (map_formula map_fact) a) (map (map_formula map_fact) d)"

fun ground_ac_name :: "plan_action \<Rightarrow> nat \<Rightarrow> string" where
  "ground_ac_name (PAction n args) i =
    pad op_prefix_pad (show i) @ (CHR ''/'' # n) @ ((CHR ''-'' # arg_str args))"

definition ground_ac :: "plan_action \<Rightarrow> nat \<Rightarrow> ast_action_schema" where
  "ground_ac \<pi> i =
    (let ga = resolve_instantiate \<pi> in
    Action_Schema (ground_ac_name \<pi> i) [] (ga_pre ga) (ga_eff ga))"

definition ground_dom :: "ast_domain" where
  "ground_dom \<equiv> Domain
    []
    (map (\<lambda>p. PredDecl p []) gr_pred_ids)
    []
    (map2 ground_ac ops op_ids)"

definition ground_prob :: "ast_problem" where
  "ground_prob \<equiv> Problem
    ground_dom
    []
    (map (map_formula map_fact) (init P))
    (map_formula map_fact (goal P))"

abbreviation "gr_ac_names \<equiv> map2 ground_ac_name ops op_ids"
definition "pa_map \<equiv> map_of (zip gr_ac_names ops)"

fun restore_ground_pa :: "plan_action \<Rightarrow> plan_action" where
  "restore_ground_pa (PAction n args) = the (pa_map n)"

abbreviation restore_ground_plan :: "plan_action list \<Rightarrow> plan_action list" where
  "restore_ground_plan \<pi>s \<equiv> map restore_ground_pa \<pi>s"

end

locale wf_grounder = grounder +
  assumes
    wf_problem and
    facts_dist: "distinct facts" and
    all_facts: "set facts \<supseteq> {a. achievable a}" and
    facts_wf: "list_all1 (wf_fmla_atom objT) facts" and (* If "set facts = {a. achievable a}", this follows. *)
    ops_dist: "distinct ops" and
    ops_correct: "set ops \<supseteq> {\<pi>. applicable \<pi>}" and
    ops_wf: "list_all1 wf_plan_action ops" (* If "set ops = {\<pi>. applicable \<pi>}", this follows. *)

abbreviation (in grounder) "D\<^sub>G \<equiv> ground_dom"
abbreviation (in grounder) "P\<^sub>G \<equiv> ground_prob"

sublocale wf_grounder \<subseteq> wf_ast_problem P
  apply (unfold_locales)
  using wf_grounder_axioms wf_grounder_def by blast

sublocale grounder \<subseteq> dg: ast_domain D\<^sub>G .
sublocale grounder \<subseteq> pg: ast_problem P\<^sub>G .

subsection \<open> Alternative definitions \<close>

context grounder begin

find_theorems "(?x = predAtm ?a ?b \<Longrightarrow> ?P)"

lemma ground_pred_cond:
  "is_predAtom a \<Longrightarrow>
  (\<exists>s. ground_pred a i = Pred (padl fact_prefix_pad (show i) @ s))"
  by (cases a rule: is_predAtom.cases) simp_all

lemma ga_pre_alt: "ga_pre ga = map_formula map_fact (precondition ga)"
  by (cases ga; simp)

lemma ga_eff_alt: "ga_eff ga =
  Effect (map (map_formula map_fact) (adds (effect ga))) (map (map_formula map_fact) (dels (effect ga)))"
  by (cases ga rule: ga_eff.cases) simp

lemma ga_eff_sel [simp]:
  "adds (ga_eff ga) = map (map_formula map_fact) (adds (effect ga))"
  "dels (ga_eff ga) = map (map_formula map_fact) (dels (effect ga))"
  unfolding ga_eff_alt by simp_all

lemma ground_ac_sel [simp]:
  "ac_name (ground_ac \<pi> i) = ground_ac_name \<pi> i"
  "ac_params (ground_ac \<pi> i) = []"
  "ac_pre (ground_ac \<pi> i) = ga_pre (resolve_instantiate \<pi>)"
  "ac_eff (ground_ac \<pi> i) = ga_eff (resolve_instantiate \<pi>)"
  unfolding ground_ac_def Let_def by simp_all

lemma ground_dom_sel [simp]:
  "types D\<^sub>G = []"
  "predicates D\<^sub>G = map (\<lambda>p. PredDecl p []) gr_pred_ids"
  "consts D\<^sub>G = []"
  "actions D\<^sub>G = map2 ground_ac ops op_ids"
  unfolding ground_dom_def by simp_all

lemma ground_prob_sel [simp]:
  "domain P\<^sub>G \<equiv> D\<^sub>G"
  "objects P\<^sub>G = []"
  "init P\<^sub>G = map (map_formula map_fact) (init P)"
  "goal P\<^sub>G = map_formula map_fact (goal P)"
  unfolding ground_prob_def by simp_all

lemma restore_ground_pa_alt: "restore_ground_pa \<pi> = the (pa_map (name \<pi>))"
  by (cases \<pi>) simp

end

subsection \<open> Output format \<close>
text \<open> The output is, in fact, grounded \<close>

context grounder begin

lemma acs_grounded: "list_all1 grounded_ac (actions D\<^sub>G)"
proof
  fix x assume a: "x \<in> set (actions D\<^sub>G)"
  then obtain op i where "x = ground_ac op i" by auto
  hence "ac_params x = []" by simp
  thus "grounded_ac x" by (cases x) simp
qed

theorem ground_dom_grounded: "dg.grounded_dom"
  unfolding dg.grounded_dom_def apply (intro conjI)
     apply simp
  unfolding grounded_pred.simps apply (intro ballI)
  subgoal for x apply (cases x) by auto
   apply simp
  using acs_grounded by blast

theorem ground_prob_grounded: "pg.grounded_prob"
  using pg.grounded_prob_def ground_dom_grounded by simp

end

subsection \<open> Well-formedness \<close>

context grounder begin
end

(* TODO \<rightarrow> Utils *)
lemma map2_obtain:
  assumes "z \<in> set (map2 f xs ys)"
  obtains x y where "z = f x y" "x \<in> set xs" "y \<in> set ys"
  using assms by (induction xs ys rule: list_induct2') auto

(* TODO \<rightarrow> Utils *)
lemma map2_dist_2:
  assumes "distinct ys" "\<And>x1 x2 y1 y2. y1 \<in> set ys \<Longrightarrow> y2 \<in> set ys \<Longrightarrow> y1 \<noteq> y2 \<Longrightarrow> f x1 y1 \<noteq> f x2 y2"
  shows "distinct (map2 f xs ys)"
  using assms proof (induction xs ys rule: list_induct2')
  case (4 x xs y ys)
  hence "distinct (map2 f xs ys)" by simp

  thus ?case apply (induction xs ys rule: list_induct2') oops

context wf_grounder begin

lemma gr_preds_dis: "distinct (map pred (predicates D\<^sub>G))"
proof -

  have "gr_pred_ids ! i \<noteq> gr_pred_ids ! j" if "i \<noteq> j" "i < length (gr_pred_ids)" "j < length (gr_pred_ids)" for i j
  proof -
    have len: "length gr_pred_ids = length facts"
      unfolding fact_ids_def using nat_range_length by simp
    hence nth: "gr_pred_ids ! x = ground_pred (facts ! x) x" if "x < length facts" for x
      unfolding fact_ids_def using that nat_range_nth by simp

    have "is_predAtom (facts ! x)" if "x < length facts" for x
      using facts_wf wf_fmla_atom_alt that by fastforce
    with nth have app: "\<exists>s. gr_pred_ids ! x = Pred (padl fact_prefix_pad (show x) @ s)" if "x < length facts" for x
      using that ground_pred_cond by simp
    have "length (padl fact_prefix_pad (show x)) = fact_prefix_pad" if "x < length facts" for x
      using that fact_prefix_pad_def padl_length nat_show_len_mono
      using order_less_imp_le by metis
    hence "padl fact_prefix_pad (show i) @ s \<noteq> padl fact_prefix_pad (show j) @ t" for s t
      using that pad_show_neq by simp
    thus ?thesis using that app len by (metis predicate.inject)
  qed
  hence "distinct gr_pred_ids" using distinct_conv_nth by blast
  moreover have "map pred (predicates D\<^sub>G) = gr_pred_ids" by simp
  ultimately show ?thesis by metis
qed

lemma gr_preds_wf: "list_all1 pg.wf_predicate_decl (predicates D\<^sub>G)"
  sorry
lemma gr_acs_dis: "distinct (map ac_name (actions D\<^sub>G))"
  sorry
lemma gr_acs_wf: "list_all1 pg.wf_action_schema (actions D\<^sub>G)"
  sorry

theorem ground_dom_wf: "dg.wf_domain"
  unfolding dg.wf_domain_def apply (intro conjI)
  using dg.wf_types_def apply simp
  using gr_preds_dis apply simp
  using gr_preds_wf apply simp
  apply simp (* consts wf *)
  apply simp (* consts' types *)
  using gr_acs_dis gr_acs_wf by simp_all

theorem ground_prob_wf: "pg.wf_problem"
  unfolding pg.wf_problem_def apply (intro conjI)
  using ground_dom_wf apply simp
      apply simp (* consts + objects distinct *)
     apply simp (* objects' types *)
  oops


end

sublocale wf_grounder \<subseteq> dg: wf_ast_domain D\<^sub>G
  using ground_dom_wf
  by (simp add: wf_ast_domain_def)

sublocale wf_grounder \<subseteq> pg: wf_ast_problem P\<^sub>G
  oops


subsection \<open> Semantics \<close>

text \<open> ground locale setup \<close>

locale grounded_domain = wf_ast_domain +
  assumes grounded_dom: grounded_dom

locale grounded_problem = wf_ast_problem +
  assumes grounded_prob: grounded_prob

sublocale grounded_problem \<subseteq> grounded_domain D
  using grounded_prob grounded_prob_def by (unfold_locales) simp


subsection \<open> Properties of grounded tasks \<close>

lemma (in grounded_problem)
  assumes "wf_plan_action (PAction n args)"
  shows "args = []"
  oops

lemma (in grounded_problem)
  assumes "wf_plan_action \<pi>"
  obtains ac where
    "ac \<in> set (actions D)"
    "wf_plan_action (PAction n [])"
    "resolve_instantiate \<pi> = instantiate_action_schema ac []"
  oops





subsection \<open> Code Setup \<close>

lemmas pddl_ground_code =
  grounder.fact_ids_def
  grounder.fact_prefix_pad_def
  grounder.op_ids_def
  grounder.op_prefix_pad_def
  grounder.ground_pred.simps
  grounder.map_fact.simps
  grounder.ga_pre.simps
  grounder.ga_eff.simps
  grounder.ground_ac_def
  grounder.ground_dom_def
  grounder.ground_prob_def
  grounder.ground_ac_name.simps
  grounder.fact_map_def
  grounder.pa_map_def
  grounder.restore_ground_pa.simps
declare pddl_ground_code[code]


end