theory Milestones
imports Main Running_Example
begin

section \<open>Minimum Viable Product\<close>

text \<open>13.12.24: Normalization\<close>

lemma "ast_problem.valid_plan P \<pi> \<Longrightarrow> ast_problem.valid_plan (detype_prob P) \<pi>"
  oops

text \<open>20.12.24: Relaxed Reachability \<close>

lemma
  assumes "ast_problem.wf_problem P"
          "ast_problem.plan_action_path P (set (init P)) \<pi>s s'"
          "s' \<^sup>c\<TTurnstile>\<^sub>= Atom (predAtm prd params)"
  obtains s'' where
    "ast_problem.plan_action_path (relax_prob P) (set (init (relax_prob P))) \<pi>s s''"
    "s'' \<^sup>c\<TTurnstile>\<^sub>= Atom (predAtm prd params)"

text \<open>27.12.24: Datalog translation\<close>


section \<open>Helmert's Rule Decomposition\<close>




section \<open>Tree Decomposition\<close>



section \<open>"iterated"\<close>








end