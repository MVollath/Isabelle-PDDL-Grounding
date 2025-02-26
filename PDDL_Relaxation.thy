theory PDDL_Relaxation
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    Formula_Normalization Utils AbLa_alts
begin

(* This is only defined for pure conjunctive clauses. *)
fun remove_neg_lits :: "'a formula \<Rightarrow> 'a formula" where
  "remove_neg_lits (\<^bold>\<not>\<bottom>) = (\<^bold>\<not>\<bottom>)" |
  "remove_neg_lits (Atom a \<^bold>\<and> c) = (Atom a \<^bold>\<and> remove_neg_lits c)" |
  "remove_neg_lits (\<^bold>\<not>(Atom a) \<^bold>\<and> c) = remove_neg_lits c"

fun relax_eff :: "'a ast_effect \<Rightarrow> 'a ast_effect" where
  "relax_eff (Effect a b) = Effect a []"

fun relax_ac :: "ast_action_schema \<Rightarrow> ast_action_schema" where
  "relax_ac (Action_Schema n params pre eff) =
    Action_Schema n params (remove_neg_lits pre) (relax_eff eff)"






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