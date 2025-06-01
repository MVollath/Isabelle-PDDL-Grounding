theory PDDL_Sema_Supplement
  imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
  Utils Formula_Utils
begin

subsection \<open> sugar \<close>

(* not much here yet *)
find_theorems name: "wf_ast_domain."
find_theorems name: "wf_ast_problem."

(* wf_domain unfolded and split *)
lemmas (in wf_ast_domain) wf_D = conj_split_7[OF wf_domain[unfolded wf_domain_def]]

(* wf_problem unfolded and split, but omitting the first fact "wf_domain" *)
lemmas (in wf_ast_problem) wf_P =
  conj_split_5[OF wf_problem[unfolded wf_problem_def, THEN conjunct2]]

lemmas (in wf_ast_problem) wf_DP = wf_D wf_domain wf_P

declare ast_problem.I_def[simp]

subsection \<open> Accessor functions \<close>

(* what's the builtin way? *)
fun un_Atom :: "'a formula \<Rightarrow> 'a" where
  "un_Atom (Atom x) = x" |
  "un_Atom _ = undefined"

abbreviation "unPredAtom \<equiv> predicate \<circ> un_Atom"

abbreviation (input) get_t :: "type \<Rightarrow> name" where
    "get_t T \<equiv> hd (primitives T)"
lemma get_t_alt: "get_t (Either (t # ts)) = t"
  by simp

lemma is_predAtom_decomp:
  "is_predAtom a \<longleftrightarrow> (\<exists>p xs. a = Atom (predAtm p xs))"
  apply (cases a)
  subgoal for x
    by (cases x) simp_all
  by simp_all

abbreviation (in ast_domain) pred_names :: "name list" where
    "pred_names \<equiv> map (predicate.name \<circ> pred) (predicates D)"

abbreviation (in ast_problem) "all_consts \<equiv> consts D @ objects P"

subsection \<open>Alternative definitions\<close>

text \<open>Alternative definitions. Most of these just remove pattern matching
  from functions, e.g. a function "add (x, y) = x + y" would be turned into
  "add p = fst p + snd p".
  They are often unnecessary because you can just apply "cases" in a proof.
  Others functions are only well-defined if a certain condition holds. The _cond-lemmas
  help resolve it directly. \<close>

abbreviation "map_atom_fmla \<equiv> map_formula \<circ> map_atom"

abbreviation "ac_name \<equiv> ast_action_schema.name"
abbreviation "ac_params \<equiv> ast_action_schema.parameters"
abbreviation "ac_pre \<equiv> ast_action_schema.precondition"
abbreviation "ac_eff \<equiv> ast_action_schema.effect"

context ast_domain begin
lemma wf_fmla_alt: "wf_fmla tyt \<phi> = (\<forall>a\<in>atoms \<phi>. wf_atom tyt a)"
      by (induction \<phi>) auto

(* unnecessary? *)
lemma apply_effect_alt: "apply_effect \<epsilon> s = (s - set (dels \<epsilon>)) \<union> (set (adds \<epsilon>))"
  by (cases \<epsilon>; simp_all)

lemma subtype_edge_swap: "subtype_edge = prod.swap"
  by (intro ext; auto)

lemma subtype_rel_alt: "subtype_rel = (set (types D))\<inverse>"
  unfolding subtype_rel_def
  by (subst subtype_edge_swap; auto)

lemma subtype_rel_star_alt: "subtype_rel\<^sup>* = ((set (types D))\<^sup>*)\<inverse>"
    using subtype_rel_alt rtrancl_converse by simp

(* useless? *)
lemmas wf_atom_deep = wf_atom.simps[unfolded wf_pred_atom.simps]

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

definition (in -) ac_tsubst :: "(variable \<times> type) list \<Rightarrow> object list \<Rightarrow> (PDDL_STRIPS_Semantics.term \<Rightarrow> object)" where
  [simp]: "ac_tsubst params args \<equiv> ast_domain.subst_term (the \<circ> (map_of (zip (map fst params) args)))"

lemma instantiate_action_schema_alt: "instantiate_action_schema ac args = Ground_Action
  (map_atom_fmla (ac_tsubst (ac_params ac) args) (ac_pre ac))
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
    (map_atom_fmla (ac_tsubst params args) pre)
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

text \<open> Note to self: ground_action_path checks if preconditions are enabled,
but plan_action_path only checks it via ground_action_path.
I don't see any redundancy. plan_action_enabled is only used in proofs. \<close>

end

subsection \<open> Further properties \<close>

lemma (in wf_ast_problem) consts_objs_disj:
  "fst ` set (consts D) \<inter> fst ` set (objects P) = {}"
  using list.set_map wf_P(1) by auto

lemma (in wf_ast_problem) objm_le_objT: "map_of (objects P) \<subseteq>\<^sub>m objT"
proof -
  have "dom constT \<inter> dom (map_of (objects P)) = {}"
    using constT_def consts_objs_disj
    by (simp add: dom_map_of_conv_image_fst)
  thus ?thesis using objT_def
    by (simp add: map_add_comm map_le_iff_map_add_commute)  
qed

lemma (in ast_domain) bigand_wf:
  assumes "\<forall>\<phi> \<in> set \<phi>s. wf_fmla tyt \<phi>"
  shows "wf_fmla tyt (\<^bold>\<And> \<phi>s)"
  using assms by (induction \<phi>s; simp)

lemma (in ast_domain) bigor_wf:
  assumes "\<forall>\<phi> \<in> set \<phi>s. wf_fmla tyt \<phi>"
  shows "wf_fmla tyt (\<^bold>\<Or> \<phi>s)"
  using assms by (induction \<phi>s; simp)

lemma (in ast_problem) wf_wm_basic:
  "wf_world_model M \<Longrightarrow> wm_basic M"
  using wf_world_model_def wf_fmla_atom_alt wm_basic_def by metis

lemma (in wf_ast_problem) i_basic:
  "wm_basic I"
  using wf_I wf_wm_basic by simp

(* could be in ast_domain but wf_atom_mono is in ast_problem *)
lemma (in ast_problem) wf_fmla_mono:
  assumes "tys \<subseteq>\<^sub>m tys'" "wf_fmla tys \<phi>"
  shows "wf_fmla tys' \<phi>"
  using assms apply (induction \<phi>)
  apply (simp add: wf_atom_mono) by simp_all

(* could be in ast_domain but wf_fmla_atom_mono is in ast_problem *)
lemma (in ast_problem) wf_eff_mono:
  assumes "tys \<subseteq>\<^sub>m tys'" "wf_effect tys eff"
  shows "wf_effect tys' eff"
  using assms apply (cases eff)
  using wf_fmla_atom_mono by auto

text \<open> Properties of sig \<close>

abbreviation "split_pred \<equiv> (\<lambda>PredDecl p n \<Rightarrow> (p, n))"

lemma split_pred_alt: "split_pred p = (pred p, argTs p)"
  using predicate_decl.case_eq_if by auto

lemma (in ast_domain) pred_resolve:
  assumes "distinct (map pred (predicates D))"
  shows "sig p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set (predicates D)"
proof -
  let ?preds = "predicates D"
  have "map (fst \<circ> split_pred) ?preds = map pred ?preds"
    using split_pred_alt by simp
  hence dis: "distinct (map (fst \<circ> split_pred) ?preds)"
    using assms by metis

  have "PredDecl p Ts \<in> set ?preds
    \<longleftrightarrow> (p, Ts) \<in> set (map split_pred ?preds)"
    using split_pred_alt by force
  also have "... \<longleftrightarrow> map_of (map split_pred ?preds) p = Some Ts"
    using dis by simp

  ultimately show ?thesis using sig_def by simp
qed

lemmas (in wf_ast_domain) sig_Some = pred_resolve[OF wf_D(2)]

lemma (in ast_domain) sig_None:
    "sig p = None \<longleftrightarrow> p \<notin> pred ` set (predicates D)"
  proof -
    have "sig p = None \<longleftrightarrow> p \<notin> fst ` set (map split_pred (predicates D))"
      using sig_def by (simp add: map_of_eq_None_iff)
    also have "... \<longleftrightarrow> p \<notin> pred ` set (predicates D)"
      using split_pred_alt by auto
    ultimately show ?thesis by simp
  qed

text \<open> action parameters \<close>

lemma (in ast_domain) ac_tsubst_intro:
  assumes "distinct (map fst params)" "params ! i = (v, vT)" "args ! i = n" "i < length params" "i < length args"
  shows "ac_tsubst params args (term.VAR v) = n"
proof -
  have "(v, n) \<in> set (zip (map fst params) args)"
    using assms in_set_zip by fastforce
  moreover have "distinct (map fst (zip (map fst params) args))"
    using assms(1) by (simp add: map_fst_zip_take)
  ultimately have "(the \<circ> map_of (zip (map fst params) args)) v = n"
    by simp
  thus ?thesis using ac_tsubst_def by fastforce
qed

text \<open> (Plan) Action instantiation \<close>

(* only first condition matters in wf_ast_problem. See: res_aux*)
lemma (in ast_problem) wf_pa_refs_ac:
  assumes "wf_plan_action (PAction n args)"
  obtains ac where "resolve_action_schema n = Some ac" "ac \<in> set (actions D)"
    "ac_name ac = n" "action_params_match ac args"
  using assms apply (cases "resolve_action_schema n")
   apply simp
  using resolve_action_schema_def index_by_eq_SomeD by fastforce

lemma (in wf_ast_domain) res_aux:
  "resolve_action_schema n = Some ac \<longleftrightarrow>
     ac \<in> set (actions D) \<and> ac_name ac = n"
  by (simp add: resolve_action_schema_def wf_D(6))

theorem (in wf_ast_problem) wf_resolve_instantiate:
  assumes "wf_plan_action \<pi>"
  shows "wf_ground_action (resolve_instantiate \<pi>)"
proof (cases \<pi>)
  case [simp]: (PAction n args)
  with assms obtain ac where
    "resolve_action_schema n = Some ac" and
    "action_params_match ac args" and
    "ac \<in> set (actions D)"
    using wf_pa_refs_ac by metis
  thus ?thesis using wf_D(7) wf_instantiate_action_schema by simp
qed

theorem (in wf_ast_problem) wf_execute_stronger:
    assumes "wf_plan_action \<pi>"
    assumes "wf_world_model s"
    shows "wf_world_model (execute_plan_action \<pi> s)"
  proof (cases \<pi>)
    case [simp]: (PAction name args)
    from assms(1) have "wf_ground_action (resolve_instantiate \<pi>)"
      using wf_resolve_instantiate by blast
    thus ?thesis
      apply (simp add: execute_plan_action_def execute_ground_action_def)
      apply (rule wf_apply_effect)
      apply (cases "resolve_instantiate \<pi>"; simp)
      by (rule \<open>wf_world_model s\<close>)
  qed

text \<open> Semantics \<close>

lemma (in ast_problem) plan_action_path_append_intro:
  assumes "plan_action_path M1 \<pi>s M2 \<and> plan_action_path M2 \<mu>s M3"
  shows "plan_action_path M1 (\<pi>s @ \<mu>s) M3"
  using assms apply (induction \<pi>s arbitrary: M1)
  using plan_action_path_def apply simp
  using plan_action_path_def plan_action_path_Cons
  by (metis append_Cons)

lemma (in ast_problem) plan_action_path_append_elim:
  assumes "plan_action_path M1 (\<pi>s @ \<mu>s) M3"
  shows "\<exists>M2. plan_action_path M1 \<pi>s M2 \<and> plan_action_path M2 \<mu>s M3"
using assms by (induction \<pi>s arbitrary: M1) auto

lemma (in wf_ast_problem) valid_plan_from_Cons[simp]:
  "valid_plan_from M (\<pi> # \<pi>s)
    \<longleftrightarrow> valid_plan_from (execute_plan_action \<pi> M) \<pi>s \<and> plan_action_enabled \<pi> M"
  using valid_plan_from_def by auto

lemma (in wf_ast_problem) valid_plan_from_snoc:
  "valid_plan_from M (\<pi>s @ [\<pi>])
    \<longleftrightarrow> (\<exists>M'. plan_action_path M \<pi>s M' \<and> plan_action_enabled \<pi> M' \<and>
    execute_plan_action \<pi> M' \<^sup>c\<TTurnstile>\<^sub>= goal P)"
  using valid_plan_from_def by (induction \<pi>s arbitrary: M; simp)

lemma entail_adds_irrelevant:
  assumes "wm_basic M" "wm_basic A"
          "A \<inter> Atom ` atoms \<F> = {}"
  shows "M \<union> A \<^sup>c\<TTurnstile>\<^sub>= \<F> \<longleftrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<F>"
proof -
  from assms(3) have "valuation (M \<union> A) \<Turnstile> \<F> \<longleftrightarrow> valuation M \<Turnstile> \<F>"
  proof (induction \<F>)
    case (Atom x)
    thus ?case unfolding valuation_def by (cases x) simp_all
  qed auto
  moreover have "wm_basic (M \<union> A)" using assms(1-2) wm_basic_def by blast
  ultimately show ?thesis using assms valuation_iff_close_world by metis
qed

lemma entail_dels_irrelevant:
  assumes "wm_basic M" "wm_basic D"
          "D \<inter> Atom ` atoms \<F> = {}"
  shows "M - D \<^sup>c\<TTurnstile>\<^sub>= \<F> \<longleftrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<F>"
proof -
  from assms(3) have "valuation (M - D) \<Turnstile> \<F> \<longleftrightarrow> valuation M \<Turnstile> \<F>"
  proof (induction \<F>)
    case (Atom x)
    thus ?case unfolding valuation_def by (cases x) simp_all
  qed auto
  moreover have "wm_basic (M - D)" using assms(1-2) wm_basic_def by blast
  ultimately show ?thesis using assms valuation_iff_close_world by metis
qed

subsection \<open>PDDL Instance Relationships\<close>

text \<open>This subsection concerns itself mostly with relationships between two PDDL instances
  (domains or problems). They are of particular interest since the normalization steps produce
  new instances that retain some of the previous properties.\<close>

lemma co_fmla_wf:
  assumes "\<And>a. ast_domain.wf_atom d1 tyt1 a \<Longrightarrow> ast_domain.wf_atom d2 tyt2 a"
  shows "ast_domain.wf_fmla d1 tyt1 \<phi> \<Longrightarrow> ast_domain.wf_fmla d2 tyt2 \<phi>"
  using assms apply (induction \<phi>)
  using ast_domain.wf_fmla.simps apply metis+
  done

lemma co_fmla_atom_wf:
  assumes "\<And>a. ast_domain.wf_atom d1 tyt1 a \<Longrightarrow> ast_domain.wf_atom d2 tyt2 a"
  shows "ast_domain.wf_fmla_atom d1 tyt1 \<phi> \<Longrightarrow> ast_domain.wf_fmla_atom d2 tyt2 \<phi>"
  using assms co_fmla_wf ast_domain.wf_fmla_atom_alt by metis

lemma co_effect_wf:
  assumes "\<And>a. ast_domain.wf_atom d1 tyt1 a \<Longrightarrow> ast_domain.wf_atom d2 tyt2 a"
  shows "ast_domain.wf_effect d1 tyt1 \<epsilon> \<Longrightarrow> ast_domain.wf_effect d2 tyt2 \<epsilon>"
  using assms co_fmla_atom_wf ast_domain.wf_effect_alt by metis

lemma co_wm_wf:
  assumes "\<And>a. ast_domain.wf_atom (domain p1) (ast_problem.objT p1) a
    \<Longrightarrow> ast_domain.wf_atom (domain p2) (ast_problem.objT p2) a"
  shows "ast_problem.wf_world_model p1 m \<Longrightarrow> ast_problem.wf_world_model p2 m"
  using assms co_fmla_atom_wf ast_problem.wf_world_model_def by metis

subsection \<open> Formula Preds \<close>

fun fmla_preds :: "'ent atom formula \<Rightarrow> predicate set" where
  "fmla_preds (Atom (predAtm p xs)) = {p}" |
  "fmla_preds (Atom (Eq a b)) = {}" |
  "fmla_preds \<bottom> = {}" |
  "fmla_preds (\<^bold>\<not> \<phi>) = fmla_preds \<phi>" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<rightarrow> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2"

lemma fmla_preds_alt: "fmla_preds \<phi> = {p | p xs. predAtm p xs \<in> atoms \<phi>}"
  apply (induction \<phi>)
  subgoal for x
    apply (cases x; simp_all)
    done
  by auto


lemma map_preserves_fmla_preds: "fmla_preds F = fmla_preds ((map_formula \<circ> map_atom) f F)"
proof (induction F)
  case (Atom x)
  thus ?case by (cases x) simp_all
qed auto

lemma notin_fmla_preds_notin_atoms: "p \<notin> fmla_preds \<phi> \<Longrightarrow> predAtm p args \<notin> atoms \<phi>"
  using fmla_preds_alt by blast


end