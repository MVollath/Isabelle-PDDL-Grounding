theory Grounded_PDDL
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    PDDL_Sema_Supplement
    Utils
begin

context wf_ast_domain begin

(* restrict types?
  restrict objects, since they could only be used in init and goal?*)

fun grounded_ac :: "ast_action_schema \<Rightarrow> bool" where
  "grounded_ac (Action_Schema n params pre effs) \<longleftrightarrow>
    params = []"

definition "grounded_dom \<equiv>
  list_all1 grounded_ac (actions D)"
end

locale grounded_domain = wf_ast_domain +
  assumes grounded_dom: grounded_dom

locale grounded_problem = wf_ast_problem +
  assumes grounded_dom: grounded_dom

sublocale grounded_problem \<subseteq> grounded_domain D
  using grounded_dom by (unfold_locales) simp


lemma (in grounded_problem)
  assumes "wf_plan_action (PlanAction n args)"
  shows "args = []"
  oops

lemma (in grounded_problem)
  assumes "wf_plan_action \<pi>"
  obtains ac where
    "ac \<in> set (actions D)"
    "wf_plan_action (PlanAction ac [])"
    "resolve_instantiate \<pi> = instantiate_action_schema ac []"
  oops







end