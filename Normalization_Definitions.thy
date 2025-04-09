theory Normalization_Definitions
  imports PDDL_Sema_Supplement
begin

text \<open> The only reason these are here instead of in their respective
  normalization files is to reduce dependencies across files.
  This benefits development on my low-RAM laptop.\<close>

(* TODO think of a better name *)
abbreviation "\<omega> \<equiv> Either [''object'']"

(*
- type hierarchy is empty (implicitly includes ''object'')
- Everything else is Either [''object''].
  This is a little superfluous: If well-formed, they can only be [''object'', ''object'', ...],
    which is semantically equivalent to [''object'']
  - predicate argument types are Either [''object''].
  - const types are Either [''object'']
  - actions parameters are detyped
    This isn't superfluous because wf_action_schema does not ensure well-formed param types. *)
definition (in ast_domain) typeless_dom :: "bool" where
  "typeless_dom \<equiv>
    types D = []
    \<and> (\<forall>p \<in> set (predicates D). \<forall>T \<in> set (argTs p). T = \<omega>)
    \<and> (\<forall>(n, T) \<in> set (consts D). T = \<omega>)
    \<and> (\<forall>ac \<in> set (actions D). \<forall>(n, T) \<in> set (ac_params ac). T = \<omega>)"

(*
- domain is detyped
- objects are detyped
*)
definition (in ast_problem) typeless_prob :: "bool" where
  "typeless_prob \<equiv>
    typeless_dom
    \<and> (\<forall>(n, T) \<in> set (objects P). T = \<omega>)"

definition (in ast_domain) "prec_normed_dom \<equiv>
  \<forall>ac \<in> set (actions D). is_conj (ac_pre ac)"

abbreviation (in ast_problem) "prec_normed_prob \<equiv> prec_normed_dom"

definition (in ast_domain) "normalized_dom \<equiv>
  typeless_dom \<and> prec_normed_dom"

definition (in ast_problem) "normalized_prob \<equiv>
  typeless_prob \<and> (is_conj (goal P)) \<and> prec_normed_prob"

lemma (in ast_problem) normed_prob_normed_dom:
  "normalized_prob \<Longrightarrow> normalized_dom"
  unfolding normalized_prob_def normalized_dom_def typeless_prob_def by blast

definition (in ast_domain) "relaxed_dom \<equiv>
  normalized_dom \<and> (\<forall>a \<in> set (actions D). is_pos_conj (ac_pre a))"

definition (in ast_problem) "relaxed_prob \<equiv>
  normalized_prob \<and> is_pos_conj (goal P) \<and>
    (\<forall>a \<in> set (actions D). is_pos_conj (ac_pre a))"

(* contexts *)

term wf_ast_problem

locale normed_dom = wf_ast_domain D for D +
  assumes normed_dom: normalized_dom

locale normed_prob = wf_ast_problem P for P +
  assumes normed_prob: normalized_prob

sublocale normed_prob \<subseteq> normed_dom D
  apply (unfold_locales)
  using normed_prob normed_prob_normed_dom by simp

(* reachability definitions *)

definition (in ast_problem) applicable :: "plan_action \<Rightarrow> bool"
  where "applicable \<pi> \<equiv> \<exists>\<pi>s M. plan_action_path I \<pi>s M \<and> \<pi> \<in> set \<pi>s"

lemma (in ast_problem) applicable_alt:
  "applicable \<pi> \<longleftrightarrow> (\<exists>\<pi>s M. plan_action_path I \<pi>s M \<and>
    plan_action_enabled \<pi> M)"
proof
  assume "applicable \<pi>"
  then obtain \<pi>s M where 1: "plan_action_path I \<pi>s M \<and> \<pi> \<in> set \<pi>s"
    unfolding applicable_def by blast
  then obtain \<pi>s' where "sublist_until \<pi>s \<pi> @ (\<pi> # \<pi>s') = \<pi>s"
    using sublist_just_until by fastforce
  with 1 show "\<exists>\<pi>s M. plan_action_path I \<pi>s M \<and>
    plan_action_enabled \<pi> M"
    using plan_action_path_append_elim plan_action_path_Cons by metis
next
  assume "\<exists>\<pi>s M. plan_action_path I \<pi>s M \<and> plan_action_enabled \<pi> M"
  then obtain \<pi>s M where 1: "plan_action_path I \<pi>s M" "plan_action_enabled \<pi> M"
    by auto
  hence "plan_action_path M [\<pi>] (execute_plan_action \<pi> M)"
    using plan_action_path_def plan_action_enabled_def
    using execute_plan_action_def execute_ground_action_def by simp
  moreover have "\<pi> \<in> set (\<pi>s @ [\<pi>])" by simp
  ultimately show "applicable \<pi>" using 1 applicable_def plan_action_path_append_intro by fast
qed

definition (in ast_problem) achievable :: "object atom formula \<Rightarrow> bool"
  where "achievable a \<equiv> \<exists>\<pi>s M. plan_action_path I \<pi>s M \<and> a \<in> M"

lemma (in wf_ast_problem) achievable_predAtm:
  "achievable a \<Longrightarrow> is_predAtom a"
  unfolding achievable_def
  using wf_I wf_plan_action_path wf_world_model_def
  unfolding wf_fmla_atom_alt by meson










end