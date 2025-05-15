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

abbreviation (in ast_problem) (input) "prec_normed_prob \<equiv> prec_normed_dom"

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

locale wf_relaxed_normed_prob = wf_ast_problem +
  assumes relaxed: relaxed_prob and normed: normalized_prob

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

lemma (in wf_ast_problem) init_achievable:
  "\<forall>a \<in> set (init P). achievable a"
proof -
  have "plan_action_path I [] I" by simp
  thus ?thesis unfolding achievable_def I_def by blast
qed

lemma (in wf_ast_problem) achievable_predAtm:
  "achievable a \<Longrightarrow> is_predAtom a"
  unfolding achievable_def
  using wf_I wf_plan_action_path wf_world_model_def
  unfolding wf_fmla_atom_alt by meson

(* grounded PDDL *)

text \<open>
  Types, constants and objects don't really matter for grounded PDDL: they can just be ignored.
  But for completeness' sake, they are restricted to be empty in grounded PDDL.
\<close>

fun grounded_pred :: "predicate_decl \<Rightarrow> bool" where
  "grounded_pred (PredDecl n args) \<longleftrightarrow> args = []"

fun grounded_ac :: "ast_action_schema \<Rightarrow> bool" where
  "grounded_ac (Action_Schema n params pre effs) \<longleftrightarrow> params = []"

definition (in ast_domain) "grounded_dom \<equiv>
  types D = [] \<and>
  list_all1 grounded_pred (predicates D) \<and>
  consts D = [] \<and>
  list_all1 grounded_ac (actions D)"

definition (in ast_problem) "grounded_prob \<equiv>
  grounded_dom \<and>
  objects P = []"


locale wf_grounded_domain = wf_ast_domain +
  assumes grounded_dom: grounded_dom

locale wf_grounded_problem = wf_ast_problem +
  assumes grounded_prob: grounded_prob

sublocale wf_grounded_problem \<subseteq> wf_grounded_domain D
  using grounded_prob grounded_prob_def by (unfold_locales) simp

lemma (in wf_grounded_problem) grounded_pa_nullary:
  "wf_plan_action (PAction n args) \<longleftrightarrow> n \<in> ac_name ` set (actions D) \<and> args = []" (is "?L \<longleftrightarrow> ?R")
proof -
  have empty: "ac_params ac = []" if "ac \<in> set (actions D)" for ac
    using that grounded_dom grounded_dom_def grounded_ac.simps
    by (metis ast_action_schema.exhaust_sel that)
  show ?thesis proof
    assume ?L
    then obtain ac where ac: "ac \<in> set (actions D)" "action_params_match ac args" "ac_name ac = n"
      using wf_pa_refs_ac by metis
    with ac show ?R using empty action_params_match_def by auto
  next
    assume ?R
    then obtain ac where ac: "ac \<in> set (actions D)" "ac_name ac = n" by blast
    with \<open>?R\<close> show ?L
      unfolding wf_plan_action_simple action_params_match_def
      using res_aux[of n ac] empty by simp
  qed
qed

(* grounded, normalized PDDL *)

locale wf_normed_grounded_domain = wf_grounded_domain +
  assumes normed_dom: prec_normed_dom

locale wf_normed_grounded_problem = wf_grounded_problem +
  assumes normed_prob: "prec_normed_prob \<and> (is_conj (goal P))"

sublocale wf_normed_grounded_problem \<subseteq> wf_normed_grounded_domain D
  using normed_prob by (unfold_locales) blast


end