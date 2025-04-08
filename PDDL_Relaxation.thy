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

subsection \<open> Alt definitions \<close>

lemma (in ast_domain) relax_ac_sel[simp]:
  "ac_name (relax_ac ac) = ac_name ac"
  "ac_params (relax_ac ac) = ac_params ac"
  "ac_pre (relax_ac ac) = relax_conj (ac_pre ac)"
  "ac_eff (relax_ac ac) = relax_eff (ac_eff ac)"
  apply (cases ac; simp)
  apply (cases ac; simp)
  apply (cases ac; simp)
  apply (cases ac; simp)
  done

lemma (in ast_domain) relax_dom_sel[simp]:
  "types DX = types D"
  "predicates DX = predicates D"
  "consts DX = consts D"
  "actions DX = map relax_ac (actions D)"
  using relax_dom_def by simp_all

lemma (in ast_problem) relax_prob_sel[simp]:
  "domain PX = relax_dom"
  "objects PX = objects P"
  "init PX = init P"
  "goal PX = relax_conj (goal P)"
  using relax_prob_def by simp_all

subsection \<open> Preserving normalization \<close>

lemmas norm_dom_defs =
  ast_domain.normalized_dom_def
  ast_domain.typeless_dom_def
  ast_domain.prec_normed_dom_def
lemmas norm_prob_defs =
  ast_problem.normalized_prob_def
  ast_problem.typeless_prob_def

lemma (in normed_dom_rx) rx_acs_typeless:
  "\<forall>ac \<in> set (map relax_ac (actions D)). \<forall>(n, T) \<in> set (ac_params ac). T = \<omega>"
  using normed_dom unfolding norm_dom_defs by simp

lemma (in normed_dom_rx) rx_acs_conjs:
  "\<forall>ac\<in>set (map relax_ac (actions D)). is_conj (ac_pre ac)"
  using normed_dom unfolding norm_dom_defs
  using relax_conj_pos[THEN pos_conj_conj] relax_ac_sel(3) relax_dom_sel(4)
  by fastforce

theorem (in normed_dom_rx) relax_dom_normed:
  "dx.normalized_dom"
  using normed_dom
  unfolding norm_dom_defs relax_dom_sel
  using rx_acs_typeless rx_acs_conjs by simp

theorem (in normed_prob_rx) relax_normed:
  "px.normalized_prob"
  using normed_prob relax_dom_normed
  unfolding norm_prob_defs ast_domain.normalized_dom_def
  unfolding relax_prob_sel
  using relax_conj_pos pos_conj_conj by blast

subsection \<open> Preserving Well-Formedness \<close>

lemma (in ast_domain_rx) rx_constT: "dx.constT = constT"
  unfolding ast_domain.constT_def by simp

lemma (in ast_domain_rx) rx_wf_atom: "dx.wf_atom = wf_atom"
  apply (rule ext; rule ext)
  subgoal for tyt x
    apply (cases x; simp)
    unfolding ast_domain.sig_def ast_domain.is_of_type_def ast_domain.of_type_def
      ast_domain.subtype_rel_def relax_dom_sel by blast
  done

lemma (in ast_domain_rx) rx_wf_fmla: "dx.wf_fmla = wf_fmla"
  apply (rule ext; rule ext)
  subgoal for tyt x
    apply (induction x; simp add: rx_wf_atom)
    done
  done

lemma (in ast_domain_rx) rx_wf_fmla_atom: "dx.wf_fmla_atom = wf_fmla_atom"
  unfolding ast_domain.wf_fmla_atom_alt rx_wf_fmla ..

lemma (in ast_domain_rx) rx_wf_eff: "dx.wf_effect = wf_effect"
  apply (rule ext; rule ext)
  subgoal for tyt eff
    apply (cases eff; simp)
    unfolding rx_wf_fmla_atom ..
  done

lemma (in ast_domain) relax_fmla_wf:
  "is_conj F \<Longrightarrow> wf_fmla tyt F \<Longrightarrow> wf_fmla tyt (relax_conj F)"
  apply (induction F) apply simp apply simp
  subgoal for F
    apply (cases F) apply simp_all
    done
  subgoal for F1
    apply (cases F1) apply simp_all
    done
  by simp_all

lemma (in ast_domain) relax_eff_wf:
  "wf_effect tyt eff \<Longrightarrow> wf_effect tyt (relax_eff eff)"
  by (cases eff) simp

lemma (in ast_problem_rx) rx_objT: "px.objT = objT"
  unfolding ast_problem.objT_def rx_constT relax_prob_sel ..

lemma (in ast_domain) relax_ac_names:
  "map ac_name (actions D) = map ac_name (map relax_ac (actions D))"
  using relax_ac_sel(1) by simp

lemma (in ast_domain_rx) relax_ac_wf:
  assumes "wf_action_schema a" "is_conj (ac_pre a)"
  shows "dx.wf_action_schema (relax_ac a)"
  using assms apply (cases a; simp) unfolding Let_def
  apply (intro conjI)
    apply blast
  using rx_wf_fmla rx_constT relax_fmla_wf apply metis
  using rx_wf_eff rx_constT relax_eff_wf by metis

theorem (in normed_dom_rx) relax_dom_wf:
  "dx.wf_domain"
  using wf_domain
  unfolding ast_domain.wf_domain_def
  unfolding ast_domain.wf_types_def
  unfolding ast_domain.wf_predicate_decl_alt ast_domain.wf_type_alt
  unfolding relax_dom_sel
  using relax_ac_names relax_ac_wf
  using normed_dom unfolding norm_dom_defs by auto

lemma (in normed_prob_rx) rx_goal_wf:
  "dx.wf_fmla px.objT (relax_conj (goal P))"
  using wf_P(5) rx_objT rx_wf_fmla
    normed_prob[unfolded norm_prob_defs] ast_domain.relax_fmla_wf
  by metis

theorem (in normed_prob_rx) relax_wf:
  "px.wf_problem"
  using wf_problem
  unfolding ast_problem.wf_problem_def
  unfolding relax_prob_sel relax_dom_sel
  apply (intro conjI)
  using relax_dom_wf apply blast apply blast
  unfolding ast_domain.wf_type_alt apply simp apply blast
  unfolding ast_problem.wf_world_model_def
  using rx_objT rx_wf_fmla_atom relax_prob_sel(1) apply metis
  using rx_goal_wf by simp

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