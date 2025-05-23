theory Pseudo_Datalog
  imports PDDL_Sema_Supplement Normalization_Definitions
    Formula_Utils
begin

text \<open>
Here, reachability analysis is performed directly on the PDDL problem data structure, instead of
first converting it to Datalog.

The input problem is assumed to be:
  - well-formed: duh
  - normalized: preconditions and goals must be pure conjunctions, and we don't want to deal with
    the type system here.
  - relaxed: there are no negative literals in precondition clauses
    TODO: re-evaluate if the structure of the goal really matters here...
\<close>

term Action_Schema
(* (name: name)
  (parameters: "(variable \<times> type) list")
  (precondition: "term atom formula")
  (effect: "term ast_effect") *)

term ast_domain.instantiate_action_schema

datatype action_clause = AClause
  (name: name)
  (parameters: "(variable \<times> type) list")
  (pred_pre: "term atom formula list")
  (cond_pre: "term atom formula list")
  (pos: "term atom formula list")

definition pos_lits_of :: "'a atom formula \<Rightarrow> 'a atom formula list" where
  "pos_lits_of F = filter is_predAtom (un_and F)"
definition cond_lits_of :: "'a atom formula \<Rightarrow> 'a atom formula list" where
  "cond_lits_of F = filter (HOL.Not \<circ> is_predAtom) (un_and F)"


  



fun as_action_clause :: "ast_action_schema \<Rightarrow> action_clause" where
  "as_action_clause (Action_Schema n params pre (Effect a d)) =
    AClause n params (filter is_predAtom (un_and pre)) [] a"




context ast_problem begin
end


subsection \<open> Proofs \<close>

lemma "set (un_and xs) = set (pos_lits_of xs) \<union> set (cond_lits_of xs)"
  unfolding pos_lits_of_def cond_lits_of_def
  apply (induction "un_and xs") apply simp
  by auto


context wf_relaxed_normed_prob begin
end


end