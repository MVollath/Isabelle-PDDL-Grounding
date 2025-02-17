theory Formula_Normalization
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    Type_Normalization Utils AbLa_alts DNF
begin


locale type_normed_domain = wf_ast_domain +
  assumes typeless_dom

locale type_normed_problem = wf_ast_problem +
  assumes "typeless_prob \<and> only_conj (goal P)"

context ast_domain begin

(* G for goal *)
definition "dummy_pred \<equiv> Pred (safe_prefix pred_names @ ''G'')"
definition "dummy_pred_decl \<equiv> PredDecl dummy_pred []"

fun set_pre :: "ast_action_schema \<Rightarrow> term atom formula \<Rightarrow> ast_action_schema" where
  "set_pre (Action_Schema n params _ eff) pre = Action_Schema n params pre eff"

fun split_ac :: "ast_action_schema \<Rightarrow> ast_action_schema list" where
  "split_ac ac =
    map (set_pre ac) (dnf_list (ac_pre ac))"

definition "split_acs \<equiv> concat (map split_ac (actions D))"

fun dummy_ac where "dummy_ac (c, s) =
  Action_Schema s [] c (Effect [Atom (predAtm dummy_pred [])] [])"

abbreviation "ac_names \<equiv> map ac_name (actions D)"

definition "dummy_ac_names clauses \<equiv>
  (map ((@) (safe_prefix ac_names)) (distinct_strings (length clauses)))"

definition "dummy_acs g \<equiv>
  map dummy_ac (zip (dnf_list g) (dummy_ac_names (dnf_list g)))"

end

context ast_problem begin

definition "fmla_normed_dom \<equiv>
  Domain
    (types D)
    (dummy_pred_decl # predicates D)
    (consts D)
    split_acs"


definition "fmla_normed_prob \<equiv>
  Problem fmla_normed_dom (objects P) (init P) (goal P)" (* TODO dummy goal *)

end



end