theory AbLa_alts
  imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
  Utils
begin

(* wf_domain unfolded and split *)
lemmas (in wf_ast_domain) wf_D = conj_split_7[OF wf_domain[unfolded wf_domain_def]]

(* wf_problem unfolded and split, but omitting the first fact "wf_domain" *)
lemmas (in wf_ast_problem) wf_P =
  conj_split_5[OF wf_problem[unfolded wf_problem_def, THEN conjunct2]]

lemmas (in wf_ast_problem) wf_DP = wf_D wf_P

text \<open> Accessor functions \<close>

(* what's the builtin way? *)
fun un_Atom :: "'a formula \<Rightarrow> 'a" where
  "un_Atom (Atom x) = x" |
  "un_Atom _ = undefined"

abbreviation "unPredAtom \<equiv> predicate \<circ> un_Atom"

abbreviation (input) get_t :: "type \<Rightarrow> name" where
    "get_t T \<equiv> hd (primitives T)"
lemma get_t_alt: "get_t (Either (t # ts)) = t"
  by simp

lemma is_predAtom_decomp: assumes "is_predAtom \<phi>"
  obtains p xs where "\<phi> = Atom (predAtm p xs)"
  using assms apply (cases \<phi>)
  apply (meson is_predAtom.elims(2))
  by simp_all

abbreviation "ac_name \<equiv> ast_action_schema.name"
abbreviation "ac_params \<equiv> ast_action_schema.parameters"
abbreviation "ac_pre \<equiv> ast_action_schema.precondition"
abbreviation "ac_eff \<equiv> ast_action_schema.effect"


context ast_domain begin
(* unnecessary? *)
lemma apply_effect_alt: "apply_effect \<epsilon> s = (s - set (dels \<epsilon>)) \<union> (set (adds \<epsilon>))"
  by (cases \<epsilon>; simp_all)

lemma subtype_edge_swap: "subtype_edge = prod.swap"
  by (intro ext; auto)

lemma subtype_rel_alt: "subtype_rel = (set (types D))\<inverse>"
  unfolding subtype_rel_def
  by (subst subtype_edge_swap; auto)

lemma wf_effect_alt:
    "wf_effect tyt \<epsilon> \<longleftrightarrow>
        (list_all1 (wf_fmla_atom tyt) (adds \<epsilon>))
      \<and> (list_all1 (wf_fmla_atom tyt) (dels \<epsilon>))"
  by (cases \<epsilon>; simp add: list_all_def)

abbreviation "ac_tyt a \<equiv> ty_term (map_of (ac_params a)) constT"

lemma wf_action_schema_alt: "wf_action_schema ac \<longleftrightarrow>
    distinct (map fst (ac_params ac))
  \<and> wf_fmla (ac_tyt ac) (ac_pre ac)
  \<and> wf_effect (ac_tyt ac) (ac_eff ac)"
  apply (cases ac; simp)
  unfolding Let_def by simp

(* unnecessary? *)
lemma wf_type_alt: "wf_type T \<longleftrightarrow> set (primitives T) \<subseteq> insert ''object'' (fst ` set (types D))"
  by (cases T; simp)

(* unnecessary? *)
lemma wf_predicate_decl_alt: "wf_predicate_decl pd \<longleftrightarrow> list_all1 wf_type (argTs pd)"
  by (cases pd; simp)

lemma (in wf_ast_domain) resolve_action_schema_cond:
  assumes "Action_Schema n params pre eff \<in> set (actions D)"
  shows "resolve_action_schema n = Some (Action_Schema n params pre eff)"
  using assms wf_D(6)
  by (simp add: resolve_action_schema_def)

fun subst_term_alt where
    "subst_term_alt psubst (term.VAR x) = psubst x"
  | "subst_term_alt psubst (term.CONST c) = c"

definition ac_tsubst :: "(variable \<times> type) list \<Rightarrow> object list \<Rightarrow> (PDDL_STRIPS_Semantics.term \<Rightarrow> object)" where
  "ac_tsubst params args \<equiv> subst_term (the \<circ> (map_of (zip (map fst params) args)))"

lemma instantiate_action_schema_alt: "instantiate_action_schema ac args = Ground_Action
  ((map_formula \<circ> map_atom) (ac_tsubst (ac_params ac) args) (ac_pre ac))
  (map_ast_effect (ac_tsubst (ac_params ac) args) (ac_eff ac))"
  apply (cases ac; simp)
  using ac_tsubst_def by metis

end
context ast_problem begin

lemma resolve_instantiate_alt: "resolve_instantiate \<pi> =
  instantiate_action_schema (the (resolve_action_schema (name \<pi>))) (arguments \<pi>)"
  by (cases \<pi>; simp)

lemma (in wf_ast_problem) resolve_instantiate_cond:
  assumes "Action_Schema n params pre eff \<in> set (actions D)"
  shows "resolve_instantiate (PAction n args) = Ground_Action
    ((map_formula \<circ> map_atom) (ac_tsubst params args) pre)
    (map_ast_effect (ac_tsubst params args) eff)"
  using assms apply (simp add: resolve_action_schema_cond del: instantiate_action_schema.simps)
  by (simp add: instantiate_action_schema_alt)

(* removing the redundant conjunct from the definition of wf_plan_action *)
lemma (in wf_ast_problem) wf_plan_action_simple:
  "wf_plan_action (PAction n args) \<longleftrightarrow> (case resolve_action_schema n of
    None \<Rightarrow> False | Some a \<Rightarrow> action_params_match a args)"
  apply (rule iffI)
   apply (simp_all split: option.splits)
  using wf_DP(7)
  by (metis ground_action.collapse index_by_eq_SomeD wf_instantiate_action_schema resolve_action_schema_def wf_effect_inst_alt wf_ground_action.simps)

(* unnecessary? *)
lemma (in wf_ast_problem) wf_plan_action_alt: "wf_plan_action \<pi> \<longleftrightarrow>
  (case resolve_action_schema (name \<pi>) of
    None \<Rightarrow> False |
    Some a \<Rightarrow> action_params_match a (arguments \<pi>))"
  apply (cases \<pi>)
  using wf_plan_action_simple plan_action.sel by presburger

lemma (in wf_ast_problem) wf_plan_action_cond:
  assumes "Action_Schema n params pre eff \<in> set (actions D)"
  shows "wf_plan_action (PAction n args) \<longleftrightarrow>
    action_params_match (Action_Schema n params pre eff) args"
  using assms wf_plan_action_simple resolve_action_schema_cond
  by (metis option.simps(5))

(* unnecessary? *)
lemma wf_ground_action_alt: "wf_ground_action ga \<longleftrightarrow>
  wf_fmla objT (precondition ga) \<and> wf_effect objT (effect ga)"
  by (cases ga; simp)

text \<open> ground_action_path checks if preconditions are enabled,
but plan_action_path only checks it via ground_action_path.
I don't see any redundancy. plan_action_enabled is only used in proofs. \<close>


end
end