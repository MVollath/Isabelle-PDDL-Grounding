theory PDDL_Relaxation
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    Formula_Normalization Utils AbLa_alts
begin










(* TODO: reevaluate the rest: *)

context wf_ast_domain begin
                          
fun relaxed_ac :: "ast_action_schema \<Rightarrow> bool" where
  "relaxed_ac (Action_Schema nam params pre effs) \<longleftrightarrow>
    (dels effs = [] \<and> is_STRIPS_fmla pre)"

definition "relaxed_dom \<equiv>
  list_all1 relaxed_ac (actions D)"
end

context wf_ast_problem begin

definition "relaxed_prob \<equiv>
  relaxed_dom \<and>
  is_STRIPS_fmla (goal P)"
end

locale relaxed_domain = wf_ast_domain +
  assumes relaxed_dom: relaxed_dom

locale relaxed_problem = wf_ast_problem +
  assumes relaxed_prob: relaxed_prob

sublocale relaxed_problem \<subseteq> relaxed_domain D
  using relaxed_prob relaxed_prob_def by (unfold_locales) simp



end