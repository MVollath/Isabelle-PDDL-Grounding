theory Grounding_Pipeline
  imports Type_Normalization Goal_Normalization Precondition_Normalization
    PDDL_Relaxation
begin

subsection \<open> Setting up compact notations \<close>

context ast_problem begin
thm detype_prob_sel
thm ast_problem2.prob_detyped
lemma detype_prob_wf_compact:
  "restrict_prob \<Longrightarrow> wf_problem
  \<Longrightarrow> ast_problem.wf_problem detype_prob"
  using restr_problem2.detype_prob_wf
  using restr_problem2.intro restr_problem.intro restr_problem_axioms.intro wf_ast_problem.intro
  by auto
lemma detyped_valid_iff_compact:
  "restrict_prob \<Longrightarrow> wf_problem
  \<Longrightarrow> valid_plan \<pi>s \<longleftrightarrow> ast_problem.valid_plan (detype_prob) \<pi>s"
  using restr_problem2.detyped_valid_iff
  using restr_problem2.intro restr_problem.intro restr_problem_axioms.intro wf_ast_problem.intro
  by auto

thm ast_problem.degoal_prob_sel
lemma degoal_prob_wf_compact:
  "wf_problem \<Longrightarrow> ast_problem.wf_problem (degoal_prob)"
  using wf_ast_problem3.degoal_prob_wf
  using wf_ast_problem3_def wf_ast_problem.intro by simp
lemma degoal_plan_restore_compact:
  "wf_problem \<Longrightarrow> ast_problem.valid_plan degoal_prob \<pi>s \<Longrightarrow> valid_plan (restore_plan_degoal \<pi>s)"
  using wf_ast_problem3.valid_plan_left
  using wf_ast_problem3_def wf_ast_problem.intro by simp
lemma degoaled_valid_iff_compact:
  "wf_problem \<Longrightarrow> (\<exists>\<pi>s. valid_plan \<pi>s) = (\<exists>\<pi>s'. ast_problem.valid_plan degoal_prob \<pi>s')"
  using wf_ast_problem3.degoaled_valid_iff
  using wf_ast_problem3_def wf_ast_problem.intro by simp

thm ast_problem.split_prob_sel
thm ast_problem4.prec_normed_prob
lemma split_prob_wf_compact:
  "wf_problem \<Longrightarrow> ast_problem.wf_problem (split_prob)"
  using wf_ast_problem4.split_prob_wf
  using wf_ast_problem4_def wf_ast_problem.intro by simp
lemma split_valid_iff_compact:
  "wf_problem \<Longrightarrow> (\<exists>\<pi>s. valid_plan \<pi>s) = (\<exists>\<pi>s'. ast_problem.valid_plan split_prob \<pi>s')"
  using wf_ast_problem4.split_valid_iff
  using wf_ast_problem4_def wf_ast_problem.intro by simp
lemma restore_plan_split_valid_compact:
  "wf_problem \<Longrightarrow> ast_problem.valid_plan split_prob \<pi>s \<Longrightarrow> valid_plan (restore_plan_split \<pi>s)"
  using wf_ast_problem4.restore_plan_split_valid
  using wf_ast_problem4_def wf_ast_problem.intro by simp

thm ast_problem.relax_prob_sel
lemma relax_wf_normed_compact:
  "wf_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    ast_problem.normalized_prob relax_prob \<and> ast_problem.wf_problem relax_prob"
  using normed_prob_rx.relax_normed normed_prob_rx.relax_wf
  unfolding normed_prob_rx_def normed_prob_def wf_ast_problem_def normed_prob_axioms_def
  by blast
lemma relax_achievables_compact:
  "wf_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    {a. achievable a} \<subseteq> {a. ast_problem.achievable relax_prob a}"
  using normed_prob_rx.relax_achievables
  unfolding normed_prob_rx_def normed_prob_def wf_ast_problem_def normed_prob_axioms_def
  by blast
lemma relax_applicables_compact:
  "wf_problem \<Longrightarrow> normalized_prob \<Longrightarrow>
    {\<pi>. applicable \<pi>} \<subseteq> {\<pi>. ast_problem.applicable relax_prob \<pi>}"
  using normed_prob_rx.relax_applicables
  unfolding normed_prob_rx_def normed_prob_def wf_ast_problem_def normed_prob_axioms_def
  by blast

end

subsection \<open> Normalization correctness \<close>

context ast_problem begin

definition "P\<^sub>N \<equiv> ast_problem.split_prob (ast_problem.degoal_prob detype_prob)"

definition "reconstruct_plan_norm \<pi>s \<equiv>
  ast_domain.restore_plan_degoal detype_dom
    (ast_domain.restore_plan_split (ast_problem.degoal_dom detype_prob) \<pi>s)"

text \<open> goal and precondition normalization preserve type normalization \<close>
lemma goal_norm_preserves_typeless:
  "typeless_prob \<Longrightarrow> ast_problem.typeless_prob (degoal_prob)"
  unfolding ast_problem.typeless_prob_def ast_domain.typeless_dom_def
    degoal_prob_sel degoal_dom_sel
  unfolding goal_pred_decl_def goal_ac_def by auto

lemma prec_norm_preserves_typeless:
  "typeless_prob \<Longrightarrow> ast_problem.typeless_prob (split_prob)"
  unfolding ast_problem.typeless_prob_def ast_domain.typeless_dom_def
    split_prob_sel split_dom_sel
  unfolding split_acs_def using split_ac_sel(2) by auto

text \<open> type and precondition normalization preserve goal normalization \<close>
lemma type_norm_preserves_goal_conj:
  "is_conj (goal P) \<Longrightarrow> is_conj (goal detype_prob)"
  unfolding detype_prob_sel .

lemma prec_norm_preserves_goal_conj:
  "is_conj (goal P) \<Longrightarrow> is_conj (goal split_prob)"
  unfolding split_prob_sel .

text \<open> Due to Either-types, type normalization can introduce disjunctions into preconditions,
  and it can thus potentially break precondition normalization. \<close>

text \<open> Goal normalization only preserves precondition normalization if the goal is a
  pure conjunction.\<close>

lemma goal_norm_preserves_prec_norm:
  assumes "prec_normed_prob"
    "is_conj (goal P)"
  shows "ast_problem.prec_normed_prob degoal_prob"
  using assms(1) unfolding ast_domain.prec_normed_dom_def
  unfolding degoal_prob_sel degoal_dom_sel
  unfolding goal_ac_def term_goal_def
  using map_preserves_isconj assms(2) by auto

theorem normalization_normalizes:
  "ast_problem.normalized_prob P\<^sub>N"
  unfolding ast_problem.normalized_prob_def P\<^sub>N_def
  using ast_problem2.prob_detyped
  using ast_problem.degoal_prob_sel(4) ast_problem.goal_norm_preserves_typeless
  using ast_problem.prec_norm_preserves_typeless ast_problem.prec_norm_preserves_goal_conj
    ast_problem4.prec_normed_prob by simp

theorem normalization_wf:
  "restrict_prob \<Longrightarrow> wf_problem \<Longrightarrow> ast_problem.wf_problem P\<^sub>N"
  unfolding P\<^sub>N_def
  using detype_prob_wf_compact ast_problem.degoal_prob_wf_compact ast_problem.split_prob_wf_compact
  by simp

theorem normalization_valid_iff:
  "restrict_prob \<Longrightarrow> wf_problem \<Longrightarrow>
    (\<exists>\<pi>s. valid_plan \<pi>s) \<longleftrightarrow> (\<exists>\<pi>s'. ast_problem.valid_plan P\<^sub>N \<pi>s')"
  unfolding P\<^sub>N_def
  using detype_prob_wf_compact ast_problem.degoal_prob_wf_compact
  using detyped_valid_iff_compact ast_problem.degoaled_valid_iff_compact
    ast_problem.split_valid_iff_compact by simp

theorem normalization_reconstruct:
  "restrict_prob \<Longrightarrow> wf_problem \<Longrightarrow>
    ast_problem.valid_plan P\<^sub>N \<pi>s \<Longrightarrow> valid_plan (reconstruct_plan_norm \<pi>s)"
  unfolding P\<^sub>N_def reconstruct_plan_norm_def
  using detype_prob_wf_compact ast_problem.degoal_prob_wf_compact
  using ast_problem.restore_plan_split_valid_compact ast_problem.degoal_plan_restore_compact
    detyped_valid_iff_compact
  by (metis ast_problem.degoal_prob_sel(1) detype_prob_sel(1))

end

subsection \<open> Relaxation \<close>

context ast_problem begin
lemma assumes "restrict_prob" "wf_problem"
  shows "{\<pi>. ast_problem.applicable P\<^sub>N \<pi>} \<subseteq> {\<pi>. ast_problem.applicable (ast_problem.relax_prob P\<^sub>N) \<pi>}"
  using assms normalization_normalizes normalization_wf ast_problem.relax_applicables_compact by simp

lemma assumes "restrict_prob" "wf_problem"
  shows "{a. ast_problem.achievable P\<^sub>N a} \<subseteq> {a. ast_problem.achievable (ast_problem.relax_prob P\<^sub>N) a}"
  using assms normalization_normalizes normalization_wf ast_problem.relax_achievables_compact by simp



end
end