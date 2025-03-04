theory PDDL_Relaxation
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    Utils AbLa_alts
begin

(* This is only defined for pure conjunctive clauses. *)
fun remove_neg_lits :: "'a formula \<Rightarrow> 'a formula" where
  "remove_neg_lits (Atom a) = Atom a" |
  "remove_neg_lits (\<^bold>\<not>\<bottom>) = (\<^bold>\<not>\<bottom>)" |
  "remove_neg_lits (Atom a \<^bold>\<and> c) = (Atom a \<^bold>\<and> remove_neg_lits c)" |
  "remove_neg_lits (\<^bold>\<not>(Atom a) \<^bold>\<and> c) = remove_neg_lits c" |
  "remove_neg_lits _ = undefined"

fun relax_eff :: "'a ast_effect \<Rightarrow> 'a ast_effect" where
  "relax_eff (Effect a b) = Effect a []"

fun relax_ac :: "ast_action_schema \<Rightarrow> ast_action_schema" where
  "relax_ac (Action_Schema n params pre eff) =
    Action_Schema n params (remove_neg_lits pre) (relax_eff eff)"

definition (in ast_domain) "relax_dom \<equiv>
  Domain
    (types D)
    (predicates D)
    (consts D)
    (map relax_ac (actions D))"

definition (in ast_problem) "relax_prob \<equiv>
  Problem
    relax_dom
    (objects P)
    (init P)
    (remove_neg_lits (goal P))"

subsection \<open> Code Setup \<close>

lemmas relax_code =
  ast_domain.relax_dom_def
  ast_problem.relax_prob_def

declare relax_code [code]


end