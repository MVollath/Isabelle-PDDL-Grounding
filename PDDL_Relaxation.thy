theory PDDL_Relaxation
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    Utils PDDL_Sema_Supplement Formula_Utils
begin

term is_conj

fun relax_eff :: "'a ast_effect \<Rightarrow> 'a ast_effect" where
  "relax_eff (Effect a b) = Effect a []"

fun relax_ac :: "ast_action_schema \<Rightarrow> ast_action_schema" where
  "relax_ac (Action_Schema n params pre eff) =
    Action_Schema n params (relax_conj pre) (relax_eff eff)"

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
    (relax_conj (goal P))"

subsection \<open> Contexts \<close>

text \<open> locale setup for simplified syntax \<close>

(* replace with D\<^sup>+ and P\<^sup>+ *)
abbreviation (in ast_domain) (input) "DX \<equiv> relax_dom"
abbreviation (in ast_problem) (input) "PX \<equiv> relax_prob"

locale ast_domain_rx = ast_domain
sublocale ast_domain_rx \<subseteq> dx: ast_domain DX .

locale normed_dom_rx = normed_dom
sublocale normed_dom_rx \<subseteq> dx: ast_domain DX .
(* this is later strengthened to "dx: normed_dom DX" *)
sublocale normed_dom_rx \<subseteq> ast_domain_rx .

locale ast_problem_rx = ast_problem
sublocale ast_problem_rx \<subseteq> px: ast_problem PX .
sublocale ast_problem_rx \<subseteq> ast_domain_rx D .

locale normed_prob_rx = normed_prob
sublocale normed_prob_rx \<subseteq> px : ast_problem PX.
(* this is later strengthened to "px: normed_prob PX" *)
sublocale normed_prob_rx \<subseteq> ast_problem_rx .
sublocale normed_prob_rx \<subseteq> normed_dom_rx D
  by unfold_locales

subsection \<open> Preserving normalization \<close>

theorem (in normed_dom_rx) relax_dom_normed:
  "dx.normalized_dom"
  sorry

theorem (in normed_prob_rx) relax_normed:
  "px.normalized_prob"
  sorry

subsection \<open> Preserving Well-Formedness \<close>

theorem (in normed_dom_rx) relax_dom_wf:
  "dx.wf_domain"
  sorry

theorem (in normed_prob_rx) relax_wf:
  "px.wf_problem"
  sorry

sublocale normed_dom_rx \<subseteq> dx: normed_dom DX
  apply (unfold_locales)
  using relax_dom_normed relax_dom_wf by simp_all

sublocale normed_prob_rx \<subseteq> px: normed_prob PX
  apply (unfold_locales)
  using relax_normed relax_wf by simp_all

subsection \<open> Semantics \<close>



subsection \<open> Code Setup \<close>

lemmas relax_code =
  ast_domain.relax_dom_def
  ast_problem.relax_prob_def

declare relax_code [code]


end