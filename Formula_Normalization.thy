theory Formula_Normalization
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    Type_Normalization Utils AbLa_alts
begin


locale type_normed_domain = wf_ast_domain +
  assumes typeless_dom

locale type_normed_problem = wf_ast_problem +
  assumes "typeless_prob \<and> only_conj (goal P)"

context ast_domain begin




end



end