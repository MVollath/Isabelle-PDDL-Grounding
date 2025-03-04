theory Precondition_Normalization
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    String_Shenanigans AbLa_alts DNF
begin

(*
This part helps ensure that names of the split actions are unique.
This part calculates the DNF for every precondition, only to then discard them again,
before they are later recalculated... TODO This should probably be cached using Let. *)
definition "n_clauses ac \<equiv> length (dnf_list (ast_action_schema.precondition ac))"

context ast_domain begin

definition "max_n_clauses \<equiv> Max (set (map n_clauses (actions D)))"
definition "prefix_padding \<equiv> max_length (distinct_strings max_n_clauses) + 1"

fun (in -)set_n_pre :: " ast_action_schema \<Rightarrow> string \<Rightarrow> term atom formula \<Rightarrow> ast_action_schema" where
  "set_n_pre (Action_Schema _ params _ eff) n pre
  = Action_Schema n params pre eff"


definition "split_ac_names ac n \<equiv>
  map (\<lambda>prefix. pad prefix_padding prefix @ ac_name ac) (distinct_strings n)"


fun split_ac :: "ast_action_schema \<Rightarrow> ast_action_schema list" where
  "split_ac ac =
    (let clauses = dnf_list (ac_pre ac) in
    map2 (set_n_pre ac) (split_ac_names ac (length clauses)) clauses)"

definition "split_acs \<equiv> concat (map split_ac (actions D))"

definition "split_dom \<equiv>
  Domain
    (types D)
    (predicates D)
    (consts D)
    split_acs"

definition (in ast_problem) "split_prob \<equiv>
  Problem
    split_dom
    (objects P)
    (init P)
    (goal P)"


(* it's important to be able to convert a plan for the output problem into a plan for the input problem.
  The other direction is probably (hopefully?) not important. *)

fun restore_pa_split where
  "restore_pa_split (PAction n args) = PAction (drop prefix_padding n) args"
abbreviation "restore_plan_split \<pi>s \<equiv> map restore_pa_split \<pi>s"


end

subsection \<open> Code Setup \<close>

lemmas precond_norm_code =
  n_clauses_def
  ast_domain.max_n_clauses_def
  ast_domain.prefix_padding_def
  ast_domain.split_ac_names_def
  ast_domain.split_ac.simps
  ast_domain.split_acs_def
  ast_domain.split_dom_def
  ast_problem.split_prob_def
  ast_domain.restore_pa_split.simps
declare precond_norm_code[code]

end