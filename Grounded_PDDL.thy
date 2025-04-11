theory Grounded_PDDL
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    PDDL_Sema_Supplement Normalization_Definitions
    Utils String_Shenanigans
begin

type_synonym facty = "object atom formula"

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

fun grounded_pred :: "facty \<Rightarrow> nat \<Rightarrow> predicate" where
  "grounded_pred (Atom a) i = Pred (padl fact_prefix_pad (show i) @ (CHR ''/'' # fact_str a))" |
  "grounded_pred _ _ = undefined"

abbreviation "gr_pred_ids \<equiv> map2 grounded_pred facts fact_ids"
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

fun grounded_ac :: "plan_action \<Rightarrow> nat \<Rightarrow> ast_action_schema" where
  "grounded_ac \<pi> i =
    (let ga = resolve_instantiate \<pi> in
    Action_Schema (ground_ac_name \<pi> i) [] (ga_pre ga) (ga_eff ga))"

definition ground_dom :: "ast_domain" where
  "ground_dom \<equiv> Domain
    []
    (map (\<lambda>p. PredDecl p []) gr_pred_ids)
    []
    (map2 grounded_ac ops op_ids)"

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
    ops_dist: "distinct ops" and
    ops_correct: "set ops \<supseteq> {\<pi>. applicable \<pi>}"
begin end

sublocale wf_grounder \<subseteq> wf_ast_problem P
  apply (unfold_locales)
  using wf_grounder_axioms wf_grounder_def by blast


subsection \<open> locale setup \<close>

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
  grounder.grounded_pred.simps
  grounder.map_fact.simps
  grounder.ga_pre.simps
  grounder.ga_eff.simps
  grounder.grounded_ac.simps
  grounder.ground_dom_def
  grounder.ground_prob_def
  grounder.ground_ac_name.simps
  grounder.fact_map_def
  grounder.pa_map_def
  grounder.restore_ground_pa.simps
declare pddl_ground_code[code]


end