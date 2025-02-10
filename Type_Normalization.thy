theory Type_Normalization
  imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    Utils Graph_Funs String_Shenanigans AbLa_alts
begin

subsection \<open> Input Restriction \<close>

text \<open>Even before performing normalization, we place a few restrictions on the input PDDL task.
Some of these aren't strictly necessary and will only be kept in place for the MVP:
* Restrict consts/objects to primitive types only. This isn't strictly necessary but saves me a lot
  of work, especially since I couldn't find any PDDL planning task that makes use of objects with
  Either types. (domain and problem)
* MVP: No disjunctions in goal formula: Our output format does not allow axioms, and I don't want
  to generate auxiliary actions during normalization. (problem)
* (maybe) check action signature types for well-formedness. (domain)\<close>

text \<open>Check if a formula consists of only (nested) conjunctions of literals.\<close>

fun single_type :: "type \<Rightarrow> bool" where
  "single_type (Either ts) \<longleftrightarrow> length ts = 1"
abbreviation single_types :: "('a \<times> type) list \<Rightarrow> bool" where
  "single_types os \<equiv> \<forall>(_, T) \<in> set os. single_type T"

(* This being omitted from wf_action_schema is a little annoying for me *)
definition (in ast_domain) wf_action_params :: "ast_action_schema \<Rightarrow> bool" where
  "wf_action_params a \<equiv> (\<forall>(n, t) \<in> set (parameters a). wf_type t)"

definition (in ast_domain) restrict_dom :: bool where
  "restrict_dom \<equiv> single_types (consts D)
                  \<and> list_all1 wf_action_params (actions D)"

locale restr_domain = wf_ast_domain +
  assumes restrict_dom: restrict_dom

definition (in ast_problem) restrict_prob :: bool where
  "restrict_prob \<equiv> restrict_dom
    \<and> single_types (objects P)
    \<and> only_conj (goal P)"

locale restr_problem = wf_ast_problem +
  assumes restrict_prob: restrict_prob

sublocale restr_problem \<subseteq> restr_domain "D"
  using restrict_prob restrict_prob_def by (unfold_locales) simp

subsection \<open>Type Normalization\<close>

(* TODO think of a better name *)
abbreviation "\<omega> \<equiv> Either [''object'']"

context ast_domain
begin

  (* if multiple inheritance exists, there are duplicates *)
  abbreviation "type_names \<equiv> remdups (''object'' # map fst (types D))"
  
  abbreviation pred_names :: "name list" where
    "pred_names \<equiv> map (predicate.name \<circ> pred) (predicates D)"
  
  definition pred_for_type :: "name \<Rightarrow> predicate" where
    "pred_for_type t \<equiv> Pred (safe_prefix pred_names @ t)"

  fun type_pred :: "name \<Rightarrow> predicate_decl" where
    "type_pred t = PredDecl (pred_for_type t) [\<omega>]"

  definition type_preds :: "predicate_decl list" where
    "type_preds \<equiv> map type_pred type_names"

  abbreviation supertypes_of :: "name \<Rightarrow> name list" where
    "supertypes_of \<equiv> reachable_nodes (types D)"

  abbreviation (input) type_predatm :: "'a \<Rightarrow> name \<Rightarrow> 'a atom" where
    "type_predatm x t \<equiv> predAtm (pred_for_type t) [x]"

  fun type_atom :: "'a \<Rightarrow> name \<Rightarrow> 'a atom formula" where
    "type_atom x t = Atom (type_predatm x t)"

  fun type_precond :: "variable \<times> type \<Rightarrow> term atom formula" where
    "type_precond (v, (Either ts)) = \<^bold>\<Or> (map (type_atom (term.VAR v)) ts)"

  definition param_precond :: "(variable \<times> type) list \<Rightarrow> term atom formula" where
    "param_precond params = \<^bold>\<And> (map type_precond params)"

  abbreviation detype_pred :: "predicate_decl \<Rightarrow> predicate_decl" where
    "detype_pred p \<equiv> PredDecl (pred p) (replicate (length (argTs p)) \<omega>)"

  definition detype_preds :: "predicate_decl list \<Rightarrow> predicate_decl list" where
    "detype_preds preds \<equiv> map detype_pred preds"

  fun detype_ent :: "('ent \<times> type) \<Rightarrow> ('ent \<times> type)" where
    "detype_ent (n, T) = (n, \<omega>)"

  definition detype_ents :: "('ent \<times> type) list \<Rightarrow> ('ent \<times> type) list" where
    "detype_ents params \<equiv> map detype_ent params"

  fun detype_ac :: "ast_action_schema \<Rightarrow> ast_action_schema" where
  "detype_ac (Action_Schema n params pre eff) =
    Action_Schema n (detype_ents params) (param_precond params \<^bold>\<and> pre) eff"

  definition detype_dom :: "ast_domain" where
  "detype_dom \<equiv>
    Domain
      []
      (type_preds @ detype_preds (predicates D))
      (detype_ents (consts D))
      (map detype_ac (actions D))"

  text \<open>This only works for single types on purpose.\<close>
  fun supertype_facts_for :: "(object \<times> type) \<Rightarrow> object atom formula list" where
    "supertype_facts_for (n, Either [t]) =
      map (type_atom n) (supertypes_of t)" |
    "supertype_facts_for (n, _) = undefined"

  definition supertype_facts :: "(object \<times> type) list \<Rightarrow> object atom formula list" where
    "supertype_facts objs \<equiv> concat (map supertype_facts_for objs)"
end

abbreviation (in ast_problem) "all_objects \<equiv> consts D @ objects P"
(* Supertype Facts substate *)
abbreviation (in ast_problem) "sf_substate \<equiv> set (supertype_facts all_objects)"

(* TODO remove remdups lmao *)
definition (in ast_problem) detype_prob :: "ast_problem" where
"detype_prob \<equiv> Problem
    detype_dom
    (detype_ents (objects P))
    (remdups (supertype_facts (all_objects) @ (init P)))
    (goal P)"

(*
- type hierarchy is empty (implicitly includes ''object'')
- predicate argument types are Either [''object''].
  - If the input problem is well-formed, this is superfluous and follows from types = []
- const types are Either [''object'']
  - also sort of superfluous. If well-formed, they can only be [''object'', ''object'', ...]
    which is semantically equivalent to [''object'']
- actions parameters are detyped
  - only not superfluous because wf_action_schema does not ensure well-formed param types. *)
definition (in ast_domain) typeless_dom :: "bool" where
  "typeless_dom \<equiv>
    types D = []
    \<and> (\<forall>p \<in> set (predicates D). \<forall>T \<in> set (argTs p). T = \<omega>)
    \<and> (\<forall>(n, T) \<in> set (consts D). T = \<omega>)
    \<and> (\<forall>ac \<in> set (actions D). \<forall>(n, T) \<in> set (parameters ac). T = \<omega>)"

(*
- domain is detyped
- objects are detyped
*)
definition (in ast_problem) typeless_prob :: "bool" where
  "typeless_prob \<equiv>
    typeless_dom
    \<and> (\<forall>(n, T) \<in> set (objects P). T = \<omega>)"

subsection \<open>Complete Normalization\<close>

definition (in ast_problem) normalized_prob :: "bool" where
  "normalized_prob \<equiv> typeless_prob \<and> undefined"


(* ------------------------------------- PROOFS ------------------------------------------------- *)
subsection \<open>Type Normalization Proofs\<close>

text \<open>This is only to simplify the syntax. So I can just do
   \<open>d2.some_function\<close> instead of \<open>ast_domain.some_function detype_dom\<close>.\<close>
abbreviation (in ast_domain) (input) "D2 \<equiv> detype_dom"
abbreviation (in ast_problem) (input) "P2 \<equiv> detype_prob"

locale ast_domain2 = ast_domain
sublocale ast_domain2 \<subseteq> d2: ast_domain D2 .

locale wf_ast_domain2 = wf_ast_domain
sublocale wf_ast_domain2 \<subseteq> d2: ast_domain D2 .
sublocale wf_ast_domain2 \<subseteq> ast_domain2 .

locale restr_domain2 = restr_domain
sublocale restr_domain2 \<subseteq> d2 : ast_domain D2 .
sublocale restr_domain2 \<subseteq> wf_ast_domain2
  by unfold_locales

locale ast_problem2 = ast_problem
sublocale ast_problem2 \<subseteq> p2: ast_problem P2 .
sublocale ast_problem2 \<subseteq> ast_domain2 D .

locale wf_ast_problem2 = wf_ast_problem
sublocale wf_ast_problem2 \<subseteq> p2 : ast_problem P2.
sublocale wf_ast_problem2 \<subseteq> ast_problem2 .
sublocale wf_ast_problem2 \<subseteq> wf_ast_domain2 D
  by unfold_locales

locale restr_problem2 = restr_problem
sublocale restr_problem2 \<subseteq> p2 : ast_problem P2 .
sublocale restr_problem2 \<subseteq> wf_ast_problem2
  by unfold_locales
sublocale restr_problem2 \<subseteq> restr_domain2 D
  by unfold_locales

text \<open> Alternate/simplified definitions\<close>

lemma single_type_alt: "single_type T \<longleftrightarrow> length (primitives T) = 1"
  by (cases T; simp)

(*lemma type_decomp_1: "single_type T \<Longrightarrow> \<exists>t. T = Either [t]"
  using Misc.list_decomp_1 by (cases T; auto)*)

lemma type_decomp_1: assumes "single_type T" obtains t where "T = Either [t]"
  using assms Misc.list_decomp_1 by (cases T; auto)

context ast_domain begin

lemma type_precond_alt: "type_precond p =
  \<^bold>\<Or> (map (type_atom (term.VAR (fst p))) (primitives (snd p)))"
  by (cases p; cases "snd p"; simp)

lemma detype_ent_alt: "detype_ent x = (fst x, \<omega>)"
  by (cases x; simp)

thm detype_ac.simps

lemma detype_ac_alt: "detype_ac ac = Action_Schema
  (ac_name ac) (detype_ents (ac_params ac)) (param_precond (ac_params ac) \<^bold>\<and> (ac_pre ac)) (ac_eff ac)"
  by (cases ac; simp)

lemma detype_dom_sel:
  "types D2 = []"
  "predicates D2 = type_preds @ detype_preds (predicates D)"
  "consts D2 = detype_ents (consts D)"
  "actions D2 = map detype_ac (actions D)"
  using detype_dom_def by simp_all

(* supertype_facts_for_cond *)
lemma superfacts_for_cond:
  assumes "single_type T"
  shows "supertype_facts_for (n, T) =
    map (type_atom n) (supertypes_of (get_t T))"
  using assms by (auto intro: type_decomp_1)

end
context ast_problem begin

lemma detype_prob_sel:
  "domain P2 = D2"
  "objects P2 = detype_ents (objects P)"
  "init P2 = remdups (supertype_facts (all_objects) @ (init P))"
  "goal P2 = goal P"
  using detype_prob_def by simp_all

end

(* just restrict_dom unfolded *)
lemma (in restr_domain) restr_D: "single_types (consts D)" "list_all1 wf_action_params (actions D)"
  using restrict_dom restrict_dom_def by auto

(* just restrict_prob unfolded *)
lemma (in restr_problem) restr_P: "single_types (objects P)" "only_conj (goal P)"
  using restrict_prob restrict_prob_def by auto

lemma (in restr_problem) single_t_objs: "single_types (all_objects)"
  using restr_D(1) restr_P(1) by auto

text \<open> basic properties of Ab+La \<close>

  lemma dist_pred: "distinct (map Pred names) \<longleftrightarrow> distinct names"
    by (meson distinct_map inj_onI predicate.inject)

  lemma (in wf_ast_problem) objT_Some: "(n, T) \<in> set (all_objects) \<longleftrightarrow> objT n = Some T"
  proof -
    have "distinct (map fst (all_objects))"
      using wf_P(1) by auto
    thus ?thesis using objT_alt
      by (metis map_of_eq_Some_iff)
  qed

  lemma (in wf_ast_problem) all_objs_ids_disj:
    "fst ` set (consts D) \<inter> fst ` set (objects P) = {}"
    using list.set_map wf_P(1) by auto

  lemma (in wf_ast_problem) objm_le_objT: "map_of (objects P) \<subseteq>\<^sub>m objT"
  proof -
    have "dom constT \<inter> dom (map_of (objects P)) = {}"
      using constT_def all_objs_ids_disj
      by (simp add: dom_map_of_conv_image_fst)
    thus ?thesis using objT_def
      by (simp add: map_add_comm map_le_iff_map_add_commute)  
  qed

text \<open> type system \<close>

lemma (in -) wf_object: "ast_domain.wf_type d \<omega>"
  unfolding ast_domain.wf_type.simps by simp

context ast_domain
begin

  lemma tyterm_prop: "P (ty_term varT cnstT x) \<longleftrightarrow>
    (case x of term.VAR x' \<Rightarrow> P (varT x') |
               term.CONST x' \<Rightarrow> P (cnstT x'))"
    by (simp split: term.split)

  (* TODO: improve this to _eq_Some_iff *)
  lemma tyterm_elem: "ty_term (map_of varT) (map_of cnstT) x \<noteq> None
    \<longleftrightarrow> (case x of term.VAR x' \<Rightarrow> x' \<in> fst ` set varT |
                   term.CONST x' \<Rightarrow> x' \<in> fst ` set cnstT)"
    by (simp add: map_of_in_R_iff split: term.split)

lemma "ty_term varT cnstT x = Some y
  \<longleftrightarrow> (case x of term.VAR x' \<Rightarrow> varT x' = Some y |
                 term.CONST x' \<Rightarrow> cnstT x' = Some y)"
  by (simp split: term.split)

lemma tyterm_some:
  assumes "distinct (map fst vars)" "distinct (map fst cnsts)"
  shows "ty_term (map_of vars) (map_of cnsts) x = Some y
  \<longleftrightarrow> (case x of term.VAR x' \<Rightarrow> (x', y) \<in> set vars |
                 term.CONST x' \<Rightarrow> (x', y) \<in> set cnsts)"
  using assms by (simp split: term.split)

text \<open> type_names \<close>

  lemma type_names_set[simp]: "set type_names = insert ''object'' (fst ` set (types D))"
    by auto

  lemma wf_type_iff_listed: "wf_type (Either ts) \<longleftrightarrow> (set ts \<subseteq> set (type_names))"
    using type_names_set by simp

text \<open> pred_for_type \<close>

  lemma type_preds_ids: "map pred type_preds = map pred_for_type type_names"
    using type_preds_def by simp

  lemma type_pred_refs_type: "p \<in> pred ` set type_preds \<longleftrightarrow> (\<exists>t \<in> set type_names. p = pred_for_type t)"
  proof -
    have "pred ` set type_preds = pred_for_type ` set type_names"
      by (metis type_preds_ids list.set_map)
    thus ?thesis by auto
  qed

  lemma pred_for_type_inj: "inj pred_for_type"
    using pred_for_type_def inj_def by force

  lemma pred_for_type_dis:
    assumes "distinct ts"
    shows "distinct (map pred_for_type ts)"
    using assms pred_for_type_inj by (rule map_inj_dis)

text \<open> type_preds \<close>

  lemma type_preds_dis:
    "distinct (map pred type_preds)"
    using pred_for_type_dis type_preds_ids by force

  lemma type_pred_notin: "pred_for_type t \<notin> pred ` set (predicates D)"
  proof -
    have "predicate.name (pred_for_type t) \<notin> set pred_names"
      using safe_prefix_correct predicate.sel pred_for_type_def by presburger
    thus ?thesis by force
  qed

  (* UNIV instead of set type_names to make it simpler to work with *)
  abbreviation type_pred_ids where "type_pred_ids \<equiv> (pred \<circ> type_pred) ` UNIV"
  lemma type_pred_in: "pred_for_type t \<in> type_pred_ids"
    using pred_for_type_def by simp

text \<open> detyped preds \<close>

  lemma preds_detyped:
    "\<forall>p \<in> set (predicates D2). \<forall>T \<in> set (argTs p). T = \<omega>"
    using type_preds_def detype_preds_def detype_dom_sel(2) by auto

  lemma dt_pred_id: "pred (detype_pred pd) = pred pd" by simp

  lemma dt_preds_ids:
    "map pred (detype_preds ps) = map pred ps"
    using dt_pred_id detype_preds_def by simp

  lemma tps_dt_preds_disj:
    "pred ` set type_preds \<inter> pred ` set (detype_preds (predicates D)) = {}"
  proof -
    have "pred ` set type_preds = pred_for_type ` set type_names"
      by (metis type_preds_ids list.set_map)
    moreover have "pred ` set (detype_preds (predicates D)) = pred ` set (predicates D)"
      using dt_preds_ids by (metis list.set_map)
    ultimately show ?thesis using type_pred_notin
      by (metis disjoint_iff_not_equal type_pred_refs_type)
  qed

  lemma (in wf_ast_domain) t_preds_dis:
    shows "distinct (map pred (predicates D2))"
  proof -
    (* Predicate names are unique because the original predicate names are unchanged
       and the additional predicate names are unique (based on unique type names)
       and distinct from the original predicates. *)

    have "distinct (map pred (detype_preds (predicates D)))"
      using dt_preds_ids wf_D(2) by simp
    hence "distinct (map pred (type_preds @ detype_preds (predicates D)))"
      using tps_dt_preds_disj type_preds_dis by simp
    thus ?thesis using detype_dom_sel(2) by simp
  qed

  lemma (in ast_domain2) t_preds_wf:
    "p \<in> set (predicates D2) \<longrightarrow> d2.wf_predicate_decl p"
    using preds_detyped wf_object by (cases p) auto

text \<open> detype ents \<close>

  lemma ents_detyped: "\<forall>(n, T) \<in> set (detype_ents ents). T = \<omega>"
    by (auto simp add: detype_ents_def)

  lemma t_ents_names:
    "map fst (detype_ents ents) = map fst ents"
    unfolding detype_ents_def by auto

  lemma t_ents_dis:
    assumes "distinct (map fst ents)"
    shows "distinct (map fst (detype_ents ents))"
    using assms by (metis t_ents_names)

  lemma (in ast_domain2) t_ents_wf:
    shows "(\<forall>(n,T) \<in> set (detype_ents ents). d2.wf_type T)"
    using ents_detyped wf_object by fast

(* stuff for formulas later *)

  lemma t_entT_Some:
    shows "map_of ents x \<noteq> None \<longleftrightarrow> map_of (detype_ents ents) x = Some \<omega>"
  proof -
    have "map_of ents x \<noteq> None \<longleftrightarrow> x \<in> fst ` set ents" using map_of_eq_None_iff by metis
    also have "... \<longleftrightarrow> x \<in> fst ` set (detype_ents ents)" using t_ents_names by (metis list.set_map)
    ultimately show ?thesis using map_of_single_val[OF ents_detyped]
      by metis
  qed

  lemma t_entT_None:
    shows "map_of ents x = None \<longleftrightarrow> map_of (detype_ents ents) x = None"
    using t_ents_names list.set_map map_of_eq_None_iff by metis

text \<open> predicate signatures \<open>sig\<close> \<close>

  abbreviation "split_pred \<equiv> (\<lambda>PredDecl p n \<Rightarrow> (p, n))"
  
  lemma split_pred_alt: "split_pred p = (pred p, argTs p)"
    using predicate_decl.case_eq_if by auto

  lemma (in ast_domain) pred_resolve:
    assumes "distinct (map pred preds)"
    shows "map_of (map split_pred preds) p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set preds"
  proof -
    have "map (fst \<circ> split_pred) preds = map pred preds"
      using split_pred_alt by simp
    hence dis: "distinct (map (fst \<circ> split_pred) preds)"
      using assms by metis
  
    have "PredDecl p Ts \<in> set preds
      \<longleftrightarrow> (p, Ts) \<in> set (map split_pred preds)"
      using split_pred_alt by force
    also have "... \<longleftrightarrow> map_of (map split_pred preds) p = Some Ts"
      using sig_def dis by simp
  
    ultimately show ?thesis by simp
  qed

  lemma (in wf_ast_domain) sig_Some:
    "sig p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set (predicates D)"
    using wf_D(2) pred_resolve sig_def by auto

  lemma (in ast_domain) sig_None:
    "sig p = None \<longleftrightarrow> p \<notin> pred ` set (predicates D)"
  proof -
    have "sig p = None \<longleftrightarrow> p \<notin> fst ` set (map split_pred (predicates D))"
      using sig_def by (simp add: map_of_eq_None_iff)
    also have "... \<longleftrightarrow> p \<notin> pred ` set (predicates D)"
      using split_pred_alt by auto
    ultimately show ?thesis by simp
  qed

  lemma (in wf_ast_domain2) sig2_aux:
    "d2.sig p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set type_preds \<union> set (detype_preds (predicates D))"
    using t_preds_dis pred_resolve d2.sig_def
    by (metis detype_dom_sel(2) set_union_code)

  lemma (in wf_ast_domain2) sig2_of_typepred:
    assumes "p \<in> pred ` set type_preds"
    shows "d2.sig p = Some [\<omega>]"
  proof -
    from assms obtain Ts where pd: "PredDecl p Ts \<in> set type_preds"
      by (metis image_iff predicate_decl.collapse)
    hence "PredDecl p Ts \<notin> set (detype_preds (predicates D))"
      using tps_dt_preds_disj by auto
    moreover have "Ts = [\<omega>]" using type_preds_def pd by auto
    ultimately show ?thesis using assms sig2_aux pd by blast
  qed

  lemma (in wf_ast_domain2) type_pred_sig:
    assumes "t \<in> set type_names"
    shows "d2.sig (pred_for_type t) = Some [\<omega>]"
  proof -
    let ?p = "pred_for_type t"
    from assms obtain Ts where pd: "PredDecl ?p Ts \<in> set type_preds"
      using type_preds_def by auto
    hence "PredDecl ?p Ts \<notin> set (detype_preds (predicates D))"
      using tps_dt_preds_disj by auto
    moreover have "Ts = [\<omega>]" using type_preds_def pd by auto
    ultimately show ?thesis using assms sig2_aux pd by blast
  qed


  lemma (in wf_ast_domain2) dt_preds_arity:
    assumes "sig p = Some Ts"
    shows "d2.sig p = Some (replicate (length Ts) \<omega>)"
  proof -
    from assms have "PredDecl p Ts \<in> set (predicates D)"
      by (simp add: sig_Some)
    hence 1: "PredDecl p (replicate (length Ts) \<omega>) \<in> set (detype_preds (predicates D))"
      using detype_preds_def by force
    hence "PredDecl p (replicate (length Ts) \<omega>) \<notin> set type_preds"
      using tps_dt_preds_disj by auto
    thus ?thesis using sig2_aux 1 by auto
  qed

text \<open> type maps \<close>

  lemma (in ast_domain2) t_constT_Some: "constT c \<noteq> None \<longleftrightarrow> d2.constT c = Some \<omega>"
    using t_entT_Some ast_domain.constT_def detype_dom_def by fastforce

  lemma (in ast_domain2) t_constT_None: "constT c = None \<longleftrightarrow> d2.constT c = None"
    using t_entT_None ast_domain.constT_def detype_dom_def by fastforce

  lemma (in ast_problem2) t_cnsts_objs_names: "map fst (all_objects)
    = map fst (detype_ents (consts D) @ detype_ents (objects P))"
    using t_ents_names by (metis map_append)

  lemma (in wf_ast_problem2) t_objm_le_objT:
    "map_of (objects P2) \<subseteq>\<^sub>m p2.objT"
  proof -
    have "distinct (map fst (all_objects))" using wf_P(1) by auto
    hence "distinct (map fst (consts D2 @ objects P2))" using t_cnsts_objs_names
      by (metis detype_dom_sel(3) detype_prob_sel(2))
    hence "fst ` set (objects P2) \<inter> fst ` set (consts D2) = {}"
      by auto
    hence "dom (map_of (objects P2)) \<inter> dom d2.constT = {}" using d2.constT_def
      by (simp add: dom_map_of_conv_image_fst)
    thus ?thesis using map_add_comm p2.objT_def
      by (metis detype_prob_sel(1) map_le_iff_map_add_commute)
  qed

  lemma (in ast_problem2) "p2.constT \<subseteq>\<^sub>m p2.objT"
    by (rule p2.constT_ss_objT)

  lemma (in ast_problem2) t_objT_Some: "objT c \<noteq> None \<longleftrightarrow> p2.objT c = Some \<omega>"
  proof -
    have 1: "\<forall>(x, y) \<in> set (detype_ents (consts D) @ detype_ents (objects P)). y = \<omega>"
      using ents_detyped by fastforce
    have "objT c \<noteq> None \<longleftrightarrow> c \<in> fst ` set (all_objects)" using t_cnsts_objs_names
      by (metis objT_alt map_of_eq_None_iff)
    also have "... \<longleftrightarrow> c \<in> fst ` set (detype_ents (consts D) @ detype_ents (objects P))"
      using t_cnsts_objs_names by (metis image_set)
    also have "... \<longleftrightarrow> p2.objT c = Some \<omega>" using map_of_single_val[OF 1]
      using p2.objT_alt
      by (simp add: detype_dom_def detype_prob_def)
    ultimately show ?thesis by simp
  qed

  lemma (in ast_problem2) t_objT_None: "objT c = None \<longleftrightarrow> p2.objT c = None"
    using t_entT_None ast_problem.objT_def
    by (metis detype_prob_sel(1-2) map_add_None t_constT_None)

   lemma t_tyt_const_Some:
    assumes "ty_term vT (map_of cnsts) (term.CONST x) \<noteq> None"
    shows "ty_term vT' (map_of (detype_ents cnsts)) (term.CONST x) = Some \<omega>"
    using assms t_entT_Some by (metis ty_term.simps(2))

  lemma t_tyt_var_Some:
    assumes "ty_term (map_of vars) cT (term.VAR x) \<noteq> None"
    shows "ty_term (map_of (detype_ents vars)) cT' (term.VAR x) = Some \<omega>"
    using assms t_entT_Some by (metis ty_term.simps(1))

  lemma t_tyt_Some:
    assumes "ty_term (map_of vars) (map_of cnsts) e \<noteq> None"
    shows "ty_term (map_of (detype_ents vars)) (map_of (detype_ents cnsts)) e = Some \<omega>"
    using assms by (induction e) (metis t_entT_Some ty_term.simps)+

  lemma t_tyt_None:
    assumes "ty_term (map_of vars) (map_of cnsts) e = None"
    shows "ty_term (map_of (detype_ents vars)) (map_of (detype_ents cnsts)) e = None"
    using assms by (induction e) (metis t_entT_None ty_term.simps)+

  (* See \<open>t_ac_tyt\<close> for where the assumption comes from. *)
  lemma (in ast_domain2) t_tyt_params:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "list_all2 (is_of_type tyt) params Ts"
    shows "list_all2 (d2.is_of_type tyt2) params (replicate (length Ts) \<omega>)"
  proof -
    from assms(2) have
      ls: "length params = length Ts" and
      "\<forall>i < length params. is_of_type tyt (params !i) (Ts ! i)"
      by (simp_all add: list_all2_nthD list_all2_lengthD)

    hence "\<forall>i < length params. tyt (params ! i) \<noteq> None" using is_of_type_def
      by (metis option.simps(4))
    hence 2: "\<forall>i < length params. tyt2 (params ! i) = Some \<omega>" using assms(1) by simp
    hence "\<forall>i < length params. (case tyt2 (params ! i) of Some t \<Rightarrow> d2.of_type t \<omega>)"
      by simp
    hence "\<forall>i < length params. d2.is_of_type tyt2 (params ! i) \<omega>"
      using d2.is_of_type_def 2 by fastforce
    thus ?thesis using ls
      by (simp add: list_all2_conv_all_nth)
  qed

text \<open> formulas \<close>

  thm wf_pred_atom.simps
  lemma (in wf_ast_domain2) t_atom_wf:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "wf_atom tyt a"
    shows "d2.wf_atom tyt2 a"
    using assms
  proof (induction a)
    case (predAtm p params)
    (* these follow from the definition of wf_pred_atom *)
    then obtain Ts where sigp: "sig p = Some Ts" by fastforce
    with predAtm have 1: "list_all2 (is_of_type tyt) params Ts" by simp

    let ?os = "replicate (length Ts) \<omega>"
    from assms 1 have a: "list_all2 (d2.is_of_type tyt2) params ?os"
      by (simp add: t_tyt_params)
    have b: "d2.sig p = Some ?os" using sigp by (simp add: dt_preds_arity)

    from a b show ?case by simp
  qed simp

  lemma (in wf_ast_domain2) t_fmla_wf:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "wf_fmla tyt \<phi>"
    shows "d2.wf_fmla tyt2 \<phi>"
    using assms apply (induction \<phi>)
    using t_atom_wf ast_domain.wf_fmla.simps(1) apply blast
    using ast_domain.wf_fmla.simps(2) apply blast
    using ast_domain.wf_fmla.simps(5) apply blast
    using ast_domain.wf_fmla.simps(3) apply blast
    using ast_domain.wf_fmla.simps(4) apply blast
    using ast_domain.wf_fmla.simps(6) by metis

  lemma (in wf_ast_domain2) t_fmla_atom_wf:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "wf_fmla_atom tyt \<phi>"
    shows "d2.wf_fmla_atom tyt2 \<phi>"
    using assms
    by (simp add: ast_domain.wf_fmla_atom_alt t_fmla_wf)

  

  lemma (in wf_ast_domain2) t_eff_wf:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "wf_effect tyt \<epsilon>"
    shows "d2.wf_effect tyt2 \<epsilon>"
    using assms ast_domain.wf_effect_alt t_fmla_atom_wf by blast

    lemma bigand_wf:
    assumes "\<forall>\<phi> \<in> set \<phi>s. wf_fmla tyt \<phi>"
    shows "wf_fmla tyt (\<^bold>\<And> \<phi>s)"
    using assms by (induction \<phi>s; simp)

  lemma bigor_wf:
    assumes "\<forall>\<phi> \<in> set \<phi>s. wf_fmla tyt \<phi>"
    shows "wf_fmla tyt (\<^bold>\<Or> \<phi>s)"
    using assms by (induction \<phi>s; simp)

text \<open> detype ac \<close>

  lemma ac_params_detyped:
    "\<forall>ac \<in> set (actions D2). \<forall>(n, T) \<in> set (ac_params ac). T = \<omega>"
    using detype_dom_sel(4) detype_ac_alt ents_detyped by fastforce

  lemma t_ac_name: "ac_name (detype_ac ac) = ac_name ac"
    by (cases ac; simp)
  lemma t_acs_names: "map ac_name (map detype_ac acs) = map ac_name acs"
    by (simp add: t_ac_name)
  lemma (in wf_ast_domain) t_acs_dis:
    "distinct (map ac_name (map detype_ac (actions D)))"
    using t_acs_names wf_D by metis

  lemma (in ast_domain2) t_ac_tyt:
    assumes "ty_term (map_of (ac_params a)) constT x \<noteq> None"
    shows "ty_term (map_of (ac_params (detype_ac a))) d2.constT x = Some \<omega>"
    using assms detype_ac_alt detype_dom_sel(3) t_tyt_Some ast_domain.constT_def by auto

  lemma params_ts_wf:
    assumes "wf_action_params a" "(n, T) \<in> set (ac_params a)"
    shows "wf_type T"
    using assms wf_action_params_def by auto

  lemma params_ts_exist: (* somehow this isn't trivial for the solver *)
    assumes "wf_action_params a" "(n, Either ts) \<in> set (ac_params a)"
    shows "set ts \<subseteq> set type_names"
    using assms params_ts_wf wf_type_iff_listed by blast

  lemma (in wf_ast_domain2) type_atom_wf:
    assumes "t \<in> set type_names" "tyt x = Some \<omega>"
    shows "d2.wf_fmla tyt (type_atom x t)"
  proof -
    from assms(1) have "d2.sig (pred_for_type t) = Some [\<omega>]" by (rule type_pred_sig)
    hence "d2.wf_fmla tyt (Atom (predAtm (pred_for_type t) [x]))"
      using assms(2) d2.of_type_refl d2.is_of_type_def by fastforce
    thus ?thesis by simp
  qed

  text \<open>
  1. tyt p = Some T
  2. tyt2 p = Some \<omega>
  for every type in T, the type_cond is wf:
    - the corresponding type_pred exists and has signature [\<omega>]
    - the arguments are just the variable [v], due to 2 with signatures [\<omega>]
  \<close>

  (* instead of d2.ac_tyt, we could use the same with an arbitrary value for consT *)
  lemma (in wf_ast_domain2) type_precond_wf:
    assumes "wf_action_params a" "p \<in> set (ac_params a)"
    shows "d2.wf_fmla
      (d2.ac_tyt (detype_ac a))
      (type_precond p)"
  proof -
    (* type_precond.cases? *)
    obtain n ts where p: "p = (n, Either ts)"     
      using type_precond.cases .
    let ?tyt = "ac_tyt a"
    let ?tyt2 = "d2.ac_tyt (detype_ac a)"
    let ?v = "term.VAR n"
    
    (* Not generally "Some (Either ts)", unless we assume wf_action_schema,
       because param names may not be distinct. *) 
    have "?tyt ?v \<noteq> None" using assms detype_ac_alt
      by (simp add: p weak_map_of_SomeI)
    hence "?tyt2 ?v = Some \<omega>" using t_tyt_var_Some
      by (simp add: detype_ac_alt)
    hence "\<forall>t \<in> set ts. d2.wf_fmla ?tyt2 (type_atom ?v t)"
      using assms p type_atom_wf[where tyt = ?tyt2] params_ts_exist by blast
    hence "\<forall>\<phi> \<in> set (map (type_atom ?v) ts). d2.wf_fmla ?tyt2 \<phi>"
      by simp
    hence "d2.wf_fmla ?tyt2 (type_precond (n, Either ts))"
      using d2.bigor_wf type_precond.simps by metis
    thus ?thesis using p by simp
  qed

  lemma (in wf_ast_domain2) t_param_precond_wf:
    assumes "wf_action_params a"
    shows "d2.wf_fmla
    (d2.ac_tyt (detype_ac a))
    (param_precond (ac_params a))"
  proof -
    let ?tyt2 = "d2.ac_tyt (detype_ac a)"
    have "\<forall>p \<in> set (ac_params a). d2.wf_fmla ?tyt2 (type_precond p)"
      using assms type_precond_wf by simp
    hence "\<forall>\<phi> \<in> set (map type_precond (ac_params a)). d2.wf_fmla ?tyt2 \<phi>" by simp
    thus ?thesis using d2.bigand_wf param_precond_def by metis
  qed

  text \<open>Three conditions: 1. distinct parameter names, 2. wf precondition, 3. wf effect\<close>
  lemma (in restr_domain2) t_ac_wf:
    assumes "a \<in> set (actions D)"
    shows "d2.wf_action_schema (detype_ac a)"
  proof -
    let ?a2 = "detype_ac a"
    let ?tyt = "ty_term (map_of (ac_params a)) constT"
    let ?tyt2 = "ty_term (map_of (ac_params (detype_ac a))) d2.constT"

    have tyt_om: "\<forall>x. ?tyt x \<noteq> None \<longrightarrow> ?tyt2 x = Some \<omega>" using t_ac_tyt by simp
    from assms have wfa: "wf_action_schema a" using wf_D(7) by simp

    from assms have "distinct (map fst (ac_params a))" using wfa wf_action_schema_alt by metis
    hence c1: "distinct (map fst (ac_params ?a2))" using t_ents_dis detype_ac_alt by auto

    from assms have "wf_fmla ?tyt (ac_pre a)" using wfa wf_action_schema_alt by metis
    hence c2b: "d2.wf_fmla ?tyt2 (ac_pre a)" using tyt_om t_fmla_wf by blast
    have "wf_action_params a" using restr_D(2) assms by simp
    note c2a = t_param_precond_wf[OF this]
    from c2a c2b have c2: "d2.wf_fmla ?tyt2 (ac_pre ?a2)" by (simp add: detype_ac_alt)

    from assms have wfeff: "wf_effect ?tyt (ac_eff a)" using wfa wf_action_schema_alt by metis
    hence "d2.wf_effect ?tyt2 (ac_eff a)" by (rule t_eff_wf[OF tyt_om])
    hence c3: "d2.wf_effect ?tyt2 (ac_eff ?a2)" using detype_ac_alt by simp

    from c1 c2 c3 show ?thesis using d2.wf_action_schema_alt by simp
  qed

  lemma (in restr_domain2) t_acs_wf:
    shows "(\<forall>a\<in>set (map detype_ac (actions D)). d2.wf_action_schema a)"
    using detype_dom_def wf_D t_ac_wf by simp

text \<open> supertype_facts (init) \<close>
  
  lemma (in wf_ast_domain) supertypes_listed:
    assumes "t \<in> set type_names"
    shows "set (supertypes_of t) \<subseteq> set type_names"
  proof -
    have "set (supertypes_of t) \<subseteq> insert t (snd ` set (types D))"
      using reachable_set by simp
    also have "... \<subseteq> insert t (set type_names)"
      using type_names_set wf_D(1) wf_types_def by auto
    also have "... \<subseteq> set type_names" using assms by simp
  
    ultimately show ?thesis by blast
  qed

  lemma (in restr_problem) superfacts_unfolded:
    "supertype_facts all_objects =
      concat (map (\<lambda>(n, T). map (type_atom n) (supertypes_of (get_t T))) all_objects)"
  proof -
    define sffor :: "object \<times> type \<Rightarrow> object atom formula list"
      where "sffor \<equiv> (\<lambda>(n, T). map (type_atom n) (supertypes_of (get_t T)))"
    have "\<forall>ob \<in> set all_objects. supertype_facts_for ob = sffor ob"
      using single_t_objs superfacts_for_cond sffor_def by fast
    hence "supertype_facts all_objects = concat (map sffor all_objects)"
      unfolding supertype_facts_def using map_eq_conv by (metis (mono_tags, lifting))
    thus ?thesis unfolding sffor_def by simp
  qed

  (* I could do "p2.wf_world_model (set (supertype_facts_for ent))"
     but it doesn't make it more readable imo. *)
  lemma (in restr_problem2) super_facts_for_wf:
    assumes "(n, T) \<in> set (all_objects)"
    shows "\<forall>\<phi> \<in> set (supertype_facts_for (n, T)). d2.wf_fmla_atom p2.objT \<phi>"
  proof -
    from assms have "single_type T" using single_t_objs by auto
    then obtain t where t: "T = Either [t]"
        by (metis type_decomp_1)
    have "wf_type T" using assms wf_DP(5, 9) by auto
    hence "t \<in> set type_names" using wf_type_iff_listed t by auto
    hence st_ss: "set (supertypes_of t) \<subseteq> set type_names"
      using supertypes_listed by simp
    have om: "p2.objT n = Some \<omega>"
      using assms by (metis t_objT_Some objT_Some option.distinct(1))
  
    have "\<forall>t\<in> set (supertypes_of t). d2.wf_fmla (p2.objT) (type_atom n t)"
      using type_atom_wf[where tyt = p2.objT] om st_ss by auto
    hence "\<forall>\<phi> \<in> set (map (type_atom n) (supertypes_of t)). d2.wf_fmla p2.objT \<phi>"
      by simp
    thus ?thesis using superfacts_for_cond t by simp
  qed

  lemma (in restr_problem2) super_facts_wf:
    shows "\<forall>\<phi> \<in> set (supertype_facts (all_objects)). d2.wf_fmla_atom p2.objT \<phi>"
    using super_facts_for_wf supertype_facts_def by auto

  lemma (in wf_ast_problem2) t_wm_wf: assumes "wf_world_model M" shows "p2.wf_world_model M"
    using assms ast_problem.wf_world_model_def t_fmla_atom_wf t_objT_Some
      detype_prob_sel(1) by metis

  lemma (in restr_problem2) t_init_wf:
    "p2.wf_world_model (set (init P2))"
  proof -
    from wf_P(4) t_wm_wf have "p2.wf_world_model (set (init P))" by simp
    moreover have "p2.wf_world_model sf_substate"
      using detype_dom_sel detype_prob_sel(1) super_facts_wf p2.wf_world_model_def by simp
    moreover have "set (init P2) = set (init P) \<union> sf_substate" using detype_prob_sel(3) by auto
    ultimately show ?thesis using p2.wf_world_model_def by auto
  qed

end
text \<open> Type atom/Supertype facts inclusion/exclusion/overlap \<close>

subsubsection \<open> Type pred inclusion/exclusion/overlap \<close>
(* TODO: reevaluate what is necessary, maybe use fmla_preds in proofs *)

(* \<inter>\<emptyset>\<noteq>\<notin>\<phi>*)

abbreviation "map_fmla \<equiv> map_formula \<circ> map_atom"

context ast_domain begin
lemma wf_patm_neq_type_patm:
  assumes "wf_pred_atom tyt (p, xs)"
  shows "type_predatm x t \<noteq> map_atom f (predAtm p xs)"
proof -
  from assms have "p \<in> pred ` set (predicates D)"
    using sig_None wf_pred_atom.simps by (metis option.simps(4))
  thus ?thesis using type_pred_notin by auto
qed

lemma wf_fmla_atom_neq_type_atom:
  assumes "wf_fmla_atom tyt \<phi>"
  shows "map_fmla f \<phi> \<noteq> type_atom x t"
  using assms apply (cases rule: wf_fmla_atom.cases[of \<phi>])
  using wf_patm_neq_type_patm by fastforce+

lemma wf_fmla_atom_neq_type_atom_unatm:
  assumes "wf_fmla_atom tyt \<phi>"
  shows "un_Atom (map_fmla f \<phi>) \<noteq> type_predatm x t"
  using assms apply (cases rule: wf_fmla_atom.cases[of \<phi>])
  using wf_patm_neq_type_patm by fastforce+

lemma wf_fmla_no_type_patms:
  assumes "wf_fmla tyt \<phi>"
  shows "type_predatm n t \<notin> atoms (map_fmla f \<phi>)"
proof -
  have "atoms (map_fmla f \<phi>) = (map_atom f) ` (atoms \<phi>)"
    by (simp add: formula.set_map)
  moreover have "type_predatm n t \<notin> (map_atom f) ` (atoms \<phi>)"
  using assms proof (induction \<phi>)
    case (Atom a)
    thus ?case
    proof (cases a)
      case (predAtm p vs)
      thus ?thesis using wf_patm_neq_type_patm Atom predAtm by fastforce
    qed simp (* Obviously, type_predatm n t \<noteq> Eq a b. *)
  qed auto
  ultimately show ?thesis by simp
qed

lemma (in restr_problem) sf_typeatms:
  assumes "\<psi> \<in> sf_substate"
  shows "\<exists>n t. \<psi> = type_atom n t"
  using assms superfacts_unfolded by auto

lemma "(\<forall>a \<in> S. f a \<notin> Y) \<longleftrightarrow> f ` S \<inter> Y = {}" by auto

lemma (in restr_problem) sf_disj_wf_fmla:
  assumes "wf_fmla tyt \<phi>"
  shows "sf_substate \<inter> Atom ` atoms (map_fmla f \<phi>) = {}"
  using assms sf_typeatms wf_fmla_no_type_patms by fastforce

lemma fmla_map_id: "map_fmla id \<phi> = \<phi>"
  by (simp add: atom.map_id0 formula.map_id)

lemma (in restr_problem) sf_disj_wf_fmla0:
  assumes "wf_fmla tyt \<phi>"
  shows "sf_substate \<inter> Atom ` atoms \<phi> = {}"
  using assms sf_disj_wf_fmla[where f=id] fmla_map_id by metis

lemma (in -) "map_ast_effect f (Effect A D) =
  Effect (map ((map_formula \<circ> map_atom) f) A) (map ((map_formula \<circ> map_atom) f) D)"
  by simp

lemma wf_eff_no_type_atoms:
  assumes "wf_effect tyt \<epsilon>"
  shows
    "type_atom n t \<notin> set (adds (map_ast_effect f \<epsilon>))" (is ?a) and
    "type_atom n t \<notin> set (dels (map_ast_effect f \<epsilon>))" (is ?d)
proof -
  from assms have "\<forall>\<phi> \<in> set (adds \<epsilon>). wf_fmla_atom tyt \<phi>"
    using assms by (cases \<epsilon>) simp
  hence "\<forall>\<phi> \<in> (map_fmla f) ` set (adds \<epsilon>). \<phi> \<noteq> type_atom n t"
    using wf_fmla_atom_neq_type_atom by fast
  thus ?a by (cases \<epsilon>) auto

  from assms have "\<forall>\<phi> \<in> set (dels \<epsilon>). wf_fmla_atom tyt \<phi>"
    using assms by (cases \<epsilon>) simp
  hence "\<forall>\<phi> \<in>(map_fmla f) ` set (dels \<epsilon>). \<phi> \<noteq> type_atom n t"
    using wf_fmla_atom_neq_type_atom by fast
  thus ?d by (cases \<epsilon>) auto
qed


abbreviation "is_type_patm a \<equiv> \<exists>x t. a = type_predatm x t"


lemma map_atom_preserves_istypeatm: "is_type_patm a \<longleftrightarrow> is_type_patm (map_atom f a)"
  by (cases a) auto

lemma map_fmla_preserves_istypeatm:
  assumes "\<forall>a \<in> atoms F. is_type_patm a"
  shows "\<forall>a \<in> atoms (map_fmla f F). is_type_patm a"
proof -
  have "atoms (map_fmla f F) = (map_atom f) ` (atoms F)"
    by (simp add: formula.set_map)
  thus ?thesis using assms
    apply (induction F)
    apply simp_all
       apply (metis map_atom_preserves_istypeatm)+
    done
qed

lemma map_fmla_preserves_nistypeatm:
  assumes "\<forall>a \<in> atoms F. \<not> is_type_patm a"
  shows "\<forall>a \<in> atoms (map_fmla f F). \<not> is_type_patm a"
proof -
  have "atoms (map_fmla f F) = (map_atom f) ` (atoms F)"
    by (simp add: formula.set_map)
  thus ?thesis using assms
    apply (induction F)
    apply simp_all
       apply (metis map_atom_preserves_istypeatm)+
    done
qed

lemma param_pre_typeatms:
  "\<forall> a \<in> atoms (map_fmla f (param_precond params)). \<exists>x t. a = type_predatm x t"
proof -
  let ?is_typatm = "\<lambda>a. (\<exists>x t. a = type_predatm x t)"
  have "\<forall> f \<in> set (map (type_atom (term.VAR v)) ts).
    \<forall>a \<in> atoms f. \<exists>x t. a = type_predatm x t" for v ts by auto
  hence "\<forall>a \<in> atoms (type_precond (v, (Either ts))). \<exists>x t. a = type_predatm x t"
    for v ts
    by (induction ts) auto
  hence "\<forall>a \<in> atoms (type_precond param). \<exists>x t. a = type_predatm x t" for param
    by (cases rule: type_precond.cases[of param]) simp
  hence "\<forall> f \<in> set (map type_precond params).
    \<forall>a \<in> atoms f. \<exists>x t. a = type_predatm x t" by simp
  hence "\<forall> a \<in> atoms (param_precond params). \<exists>x t. a = type_predatm x t"
    unfolding param_precond_def by (induction params) auto
  with map_fmla_preserves_istypeatm show ?thesis by blast
qed

lemma (in ast_problem) wf_wm_no_typeatms:
  "wf_world_model wm \<Longrightarrow> type_atom x t \<notin> wm"
  unfolding wf_world_model_def using wf_fmla_atom_neq_type_atom by fastforce

lemma (in ast_problem) wf_wm_disj_param_pre:
  assumes "wf_world_model wm"
  shows "wm \<inter> Atom ` atoms (map_fmla f (param_precond params)) = {}"
  using assms wf_wm_no_typeatms param_pre_typeatms by force

(* for wf init, since sf and init don't overlap *)
lemma (in restr_problem) sf_disj_wf_wm:
  assumes "wf_world_model wm"
  shows "sf_substate \<inter> wm = {}"
proof -
  from assms have "\<forall>\<phi> \<in> wm. wf_fmla_atom objT \<phi>"
    using wf_world_model_def by simp
  hence "type_atom x t \<notin> wm" for x t
    using wf_fmla_atom_neq_type_atom by fastforce
  thus ?thesis using sf_typeatms by blast
qed

lemma (in restr_problem) sf_disj_wf_eff:
  assumes "wf_effect tyt \<epsilon>"
  shows
    "sf_substate \<inter> set (adds (map_ast_effect f \<epsilon>)) = {}"
    "sf_substate \<inter> set (dels (map_ast_effect f \<epsilon>)) = {}"
  using assms sf_typeatms wf_eff_no_type_atoms by fast+

(* ------------------------------- *)

text \<open> init cond \<close>

(* super simple because of remdups *)
lemma (in restr_problem) t_init_dis: "distinct (init P2)"
  using detype_prob_sel by simp

(*proof -
  have "distinct (supertype_facts (all_objects))" sorry
  moreover have "distinct (init P)" using wf_P by simp
  moreover have "sf_substate \<inter> set (init P) = {}"
    using wf_P sf_disj_wf_wm by simp

  ultimately have "distinct (supertype_facts (all_objects) @ (init P))" by simp*)



text \<open> goal \<close>

  lemma (in wf_ast_problem2) t_goal_wf:
    "p2.wf_fmla p2.objT (goal P2)"
  proof -
    have 1: "\<forall>e. objT e \<noteq> None \<longrightarrow> p2.objT e = Some \<omega>"
      using t_objT_Some by simp
    have 2: "wf_fmla objT (goal P2)" using detype_prob_def wf_P by simp
    thus "p2.wf_fmla p2.objT (goal P2)"
      using t_fmla_wf[OF 1 2] detype_prob_def by simp
  qed

text \<open> major\<close>
  theorem (in ast_domain2) dom_detyped:
    "d2.typeless_dom"
  proof -
    have c1: "types D2 = []" using detype_dom_def by simp
    note c2 = preds_detyped
    have c3: "\<forall>(n, T) \<in> set (consts D2). T = \<omega>"
      by (simp add: detype_dom_def ents_detyped)
    note c4 = ac_params_detyped
  
    from c1 c2 c3 c4 show ?thesis
      using d2.typeless_dom_def by simp
  qed

  theorem (in ast_problem2) prob_detyped:
    "p2.typeless_prob"
  proof -
    have "\<forall>(n, T) \<in> set (objects P2). T = \<omega>"
      by (simp add: detype_prob_def ents_detyped)
    thus ?thesis using dom_detyped p2.typeless_prob_def detype_prob_def by simp
  qed

  theorem (in restr_domain2) detype_dom_wf:
    shows "d2.wf_domain"
  proof -
    (* Types are well-formed because they are simply empty. *)
    have c1: "d2.wf_types" using d2.wf_types_def detype_dom_def by simp
    note c2 = t_preds_dis
    note c3 = t_preds_wf
    note c4 = t_ents_dis[OF wf_D(4)]
    note c5 = t_ents_wf[of "consts D"]
    note c6 = t_acs_dis
    note c7 = t_acs_wf

    from c1 c2 c3 c4 c5 c6 c7 show ?thesis
      using d2.wf_domain_def detype_dom_def by auto
  qed

  theorem (in restr_problem2) detype_prob_wf:
    shows "p2.wf_problem"
  proof -
    note c1 = detype_dom_wf
    have c2: "distinct (map fst (objects P2) @ map fst (consts D2))"
      using t_ents_names wf_P(1) by (metis detype_prob_sel(2) detype_dom_sel(3))
    have c3: "\<forall>(n, y)\<in>set (objects P2). p2.wf_type y"
      using t_ents_wf detype_prob_def by fastforce
    note c4 = t_init_dis
    note c5 = t_init_wf
    note c6 = t_goal_wf
    
    from c1 c2 c3 c4 c5 c6 show ?thesis
      using p2.wf_problem_def detype_prob_def detype_dom_def by simp
  qed
end

sublocale restr_domain2 \<subseteq> d2: wf_ast_domain D2
  using detype_dom_wf wf_ast_domain.intro by simp

sublocale restr_problem2 \<subseteq> p2: wf_ast_problem P2
  using detype_prob_wf wf_ast_problem.intro by simp

subsubsection \<open> Type Normalization Preserves Semantics \<close>

context ast_domain
begin

text \<open> Supertype Enumeration \<close>

  lemma subtype_rel_star_alt: "subtype_rel\<^sup>* = ((set (types D))\<^sup>*)\<inverse>"
    using subtype_rel_alt rtrancl_converse by simp

  lemma of_type_iff_reach:
    shows "of_type (Either oT) (Either T) \<longleftrightarrow> (
      \<forall>ot \<in> set oT.
      \<exists>t \<in> set T.
        t \<in> set (supertypes_of ot))"
  proof -
    have "of_type (Either oT) (Either T) \<longleftrightarrow>
      set oT \<subseteq> ((set (types D))\<^sup>*)\<inverse> `` set T"
      using subtype_rel_star_alt of_type_def by simp
    also have "... \<longleftrightarrow>
      (\<forall>ot \<in> set oT. ot \<in> ((set (types D))\<^sup>*)\<inverse> `` set T)"
      by auto
    also have "... \<longleftrightarrow>
      (\<forall>ot \<in> set oT. \<exists>t. (ot, t) \<in> (set (types D))\<^sup>* \<and> t \<in> set T)"
      by auto
    finally show ?thesis using reachable_iff_in_star describes_rel_def by metis
  qed

end
context ast_problem
begin

  lemma (in ast_domain) single_of_type_iff:
    shows "of_type (Either [ot]) (Either T) \<longleftrightarrow> (
      \<exists>t \<in> set T.
        t \<in> set (supertypes_of ot))"
    using of_type_iff_reach by simp

  lemma (in ast_problem) obj_of_type_iff_reach:
    assumes "objT n = Some (Either oT)"
    shows  "is_obj_of_type n (Either T) \<longleftrightarrow>
      (\<forall>ot \<in> set oT.
        \<exists>t \<in> set T.
      t \<in> set (supertypes_of ot))"
    using assms is_obj_of_type_def of_type_iff_reach by auto

lemma type_atom_inj: "inj (type_atom n)"
  using type_atom.simps pred_for_type_inj
  by (simp add: inj_def)

  lemma (in ast_problem) simple_obj_of_type_iff:
    assumes "objT n = Some (Either [ot])"
    shows  "is_obj_of_type n (Either T) \<longleftrightarrow>
        (\<exists>t \<in> set T.
      t \<in> set (supertypes_of ot))"
    using assms is_obj_of_type_def single_of_type_iff by auto

lemma simple_obj_of_type_iff_fact:
  assumes "objT n = Some oT" "single_type oT"
  shows "is_obj_of_type n (Either T) \<longleftrightarrow>
    (\<exists>t \<in> set T.
    (type_atom n t) \<in> set (supertype_facts_for (n, oT)))"
proof -
  from assms(2) obtain ot where [simp]: "oT = Either [ot]"
    by (auto intro: type_decomp_1)
  hence "is_obj_of_type n (Either T) \<longleftrightarrow>
    (\<exists>t \<in> set T.
    (type_atom n t) \<in> (type_atom n) ` set (supertypes_of ot))"
    using assms simple_obj_of_type_iff type_atom_inj inj_image_mem_iff by metis
  thus ?thesis using assms(1) by simp
qed
end

context restr_problem
begin
lemma (in restr_problem2) sf_basic: "wm_basic sf_substate"
proof -
  have "sf_substate \<subseteq> set (init P2)" using detype_prob_def by simp
  moreover have "wm_basic (set (init P2))" using wm_basic_def detype_prob_wf
    using p2.wf_P(4) p2.wf_fmla_atom_alt p2.wf_world_model_def by auto
  ultimately show ?thesis using wm_basic_def by blast
qed

lemma "type_atom n t \<in> set (supertype_facts ents)
  \<Longrightarrow> \<exists>ent \<in> set ents. type_atom n t \<in> set (supertype_facts_for ent)"
  using supertype_facts_def by simp
lemma "single_type T \<Longrightarrow> type_atom n t \<in> set (supertype_facts_for (m, T)) \<Longrightarrow> n = m"
  using superfacts_for_cond type_atom.elims by auto

lemma typeatm_iff_obj_listed:
  assumes "type_atom n t \<in> sf_substate"
  obtains oT where "(n, oT) \<in> set (all_objects)"
  using assms supertype_facts_def superfacts_for_cond single_t_objs by fastforce

theorem obj_of_type_iff:
  shows "is_obj_of_type n (Either T) \<longleftrightarrow>
    (\<exists>t \<in> set T.
     type_atom n t \<in> sf_substate)"
proof
  assume L: "is_obj_of_type n (Either T)"
  moreover obtain oT where ot: "(n, oT) \<in> set (all_objects)"
    using L objT_Some is_obj_of_type_def by (cases "objT n"; simp)
  moreover have "set (supertype_facts_for (n, oT)) \<subseteq> sf_substate"
    using supertype_facts_def ot by auto
  ultimately show "\<exists>t \<in> set T. type_atom n t \<in> sf_substate"
    using simple_obj_of_type_iff_fact single_t_objs objT_Some
    by (metis case_prod_conv subset_code(1))
next
  assume R: "\<exists>t \<in> set T. type_atom n t \<in> sf_substate"
  then obtain oT where ot: "(n, oT) \<in> set (all_objects)"
    using typeatm_iff_obj_listed by auto
  from R  obtain t where tin: "t \<in> set T" and "type_atom n t \<in> sf_substate" ..
  then obtain n' T' where
    1: "type_atom n t \<in> set (supertype_facts_for (n', T'))" and
    2: "(n', T') \<in> set (all_objects)"
    using supertype_facts_def by auto
  from 2 have "single_type T'" using single_t_objs by auto
  hence "n = n'" using 1 superfacts_for_cond by auto
  moreover hence "oT = T'" using 2 ot
    by (metis objT_Some option.inject)
  ultimately have "type_atom n t \<in> set (supertype_facts_for (n, oT))" using 1 by simp
  thus "is_obj_of_type n (Either T)"
    using ot objT_Some single_t_objs tin simple_obj_of_type_iff_fact by blast
qed

lemma (in restr_problem2) obj_of_type_iff2:
  shows "is_obj_of_type n (Either T) \<longleftrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= \<^bold>\<Or>(map (type_atom n) T)"
proof -
  have "is_obj_of_type n (Either T) \<longleftrightarrow>
    (\<exists>t \<in> set T. valuation sf_substate \<Turnstile> type_atom n t)"
    using obj_of_type_iff valuation_def by simp
  also have "... \<longleftrightarrow> valuation sf_substate \<Turnstile> (\<^bold>\<Or>(map (type_atom n) T))" (* type_precond uses variables instead of objects... *)
    using BigOr_semantics by simp
  also have "... \<longleftrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= \<^bold>\<Or>(map (type_atom n) T)"
    using sf_basic valuation_iff_close_world by blast
  finally show ?thesis by auto
qed

thm action_params_match_def

lemma map_formula_bigOr: "(\<^bold>\<Or> (map (map_formula f) \<phi>s)) = map_formula f (\<^bold>\<Or> \<phi>s)"
  by (induction \<phi>s; simp_all)

lemma (in restr_problem2) obj_of_vartype_iff:
  assumes "tsubst (term.VAR v) = n"
  shows "is_obj_of_type n vT \<longleftrightarrow>
    sf_substate \<^sup>c\<TTurnstile>\<^sub>= (map_formula \<circ> map_atom) tsubst (type_precond (v, vT))"
proof -
  let ?map_subst = "(map_formula \<circ> map_atom) tsubst"
  have 1: "map (type_atom n) (primitives vT) = map (?map_subst \<circ> type_atom (term.VAR v)) (primitives vT)"
    using assms by simp
  have 2: "\<^bold>\<Or>(map (?map_subst \<circ> (type_atom (term.VAR v))) (primitives vT))
    = ?map_subst \<^bold>\<Or>(map ((type_atom (term.VAR v))) (primitives vT))"
    using map_formula_bigOr by (metis comp_apply list.map_comp)
  have "is_obj_of_type n vT \<longleftrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= \<^bold>\<Or>(map (type_atom n) (primitives vT))"
    using obj_of_type_iff2 by force
  thus ?thesis using 1 2 type_precond.simps
    by (metis type.exhaust_sel)
qed


lemma ac_tsubst_aux:
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

lemma (in restr_problem2) obj_of_vartype_iff2:
  assumes
    "distinct (map fst params)"
    "params ! i = (v, vT)" "args ! i = n"
    "i < length params" "i < length args"
  shows "is_obj_of_type n vT \<longleftrightarrow>
    sf_substate \<^sup>c\<TTurnstile>\<^sub>= (map_formula \<circ> map_atom) (ac_tsubst params args) (type_precond (v, vT))"
  using obj_of_vartype_iff ac_tsubst_aux[OF assms] by blast

(* using this logic for the next lemma *)
lemma "(b \<Longrightarrow> (c \<longleftrightarrow> d)) \<Longrightarrow> b \<and> c \<longleftrightarrow> b \<and> d" by auto
thm list_decomp_1

(* forgive me, father, for I have sinned; TODO: simplify *)
theorem (in restr_problem2) params_match_iff_type_precond:
  assumes "wf_action_schema ac"
  defines "params \<equiv> ac_params ac"
  shows "action_params_match ac args \<longleftrightarrow>
    length params = length args \<and>
    sf_substate \<^sup>c\<TTurnstile>\<^sub>= (map_formula \<circ> map_atom) (ac_tsubst params args) (param_precond params)"
proof -
  let ?leq = "length params = length args"
  define el_map where "el_map \<equiv> (map_formula \<circ> map_atom) (ac_tsubst params args)"

  have dis: "distinct (map fst params)" using assms wf_action_schema_alt by metis

  have 1: "action_params_match ac args \<longleftrightarrow>
    ?leq \<and>
    (\<forall>i < (length params). is_obj_of_type (args ! i) (snd (params ! i)))"
    using assms(2) action_params_match_def
    by (smt (verit) length_map list_all2_all_nthI list_all2_lengthD list_all2_nthD nth_map)
  {
    assume ?leq
    {
      fix i assume l: "i < length params"
      
      hence "is_obj_of_type (args ! i) (snd (params ! i))
      \<longleftrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= el_map (type_precond (params ! i))"
        using obj_of_vartype_iff2 dis \<open>?leq\<close> is_obj_of_type_def
        by (metis el_map_def prod.exhaust_sel)
    }
    hence "(\<forall>i < length params. is_obj_of_type (args ! i) (snd (params ! i))) \<longleftrightarrow>
      (\<forall>\<phi> \<in> {el_map (type_precond (params ! i)) | i. i < length params}. sf_substate \<^sup>c\<TTurnstile>\<^sub>= \<phi>)"
      by blast
    also have "... \<longleftrightarrow>
      (\<forall>\<phi> \<in> set (map (el_map \<circ> type_precond) params). sf_substate \<^sup>c\<TTurnstile>\<^sub>= \<phi>)"
      using map_set_comprehension[where f="el_map \<circ> type_precond"] by fastforce
    also have "... \<longleftrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= \<^bold>\<And>(map (el_map \<circ> type_precond) params)"
      using bigAnd_entailment by blast
    also have "... \<longleftrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= el_map (\<^bold>\<And>(map type_precond params))"
      using el_map_def bigAnd_map_atom
      by (metis list.map_comp)
    note calculation
  }
  thus ?thesis using 1 el_map_def bigAnd_map_atom
    by (metis (no_types, opaque_lifting) map_map param_precond_def)
qed


lemma
  assumes "wm_basic M"
  shows "M \<^sup>c\<TTurnstile>\<^sub>= type_atom x t \<longleftrightarrow> (valuation M) (type_predatm x t)"
  using assms valuation_iff_close_world by force

end


(* INSTANTIATE STUFF *)

(* only first condition matters in wf_ast_problem. See: res_aux*)
lemma (in ast_problem) wf_pa_refs_ac:
  assumes "wf_plan_action (PAction n args)"
  obtains ac where "resolve_action_schema n = Some ac" "ac \<in> set (actions D)" "ac_name ac = n"
  using assms wf_plan_action.simps resolve_action_schema_def index_by_eq_SomeD
  by (smt (verit, ccfv_threshold) option.case_eq_if option.collapse)


lemma (in wf_ast_problem) res_aux:
  "resolve_action_schema n = Some ac \<longleftrightarrow>
     ac \<in> set (actions D) \<and> ac_name ac = n"
  by (simp add: resolve_action_schema_def wf_DP(6))

lemma (in restr_problem2) t_resinst:
  assumes "resolve_action_schema n = Some ac"
  shows "d2.resolve_action_schema n = Some (detype_ac ac)"
proof -
  from assms have a: "ac \<in> set (actions D)"
    by (metis index_by_eq_SomeD resolve_action_schema_def)
  from assms have b: "ac_name ac = n"
    by (metis resolve_action_schema_def index_by_eq_SomeD)
  hence "ac_name (detype_ac ac) = n" by (simp add: t_ac_name)
  moreover have "detype_ac ac \<in> set (actions D2)"
    using a detype_dom_sel(4) by auto
  ultimately show ?thesis using d2.wf_D(6)
    by (simp add: d2.resolve_action_schema_def)
qed

lemma (in restr_problem2) t_resinst_inv:
  assumes "p2.resolve_action_schema n = Some ac2"
  obtains ac where
    "detype_ac ac = ac2"
    "ac \<in> set (actions D)"
    "resolve_action_schema n = Some ac"
proof -
  from assms obtain ac where ac: "detype_ac ac = ac2" and ac_in: "ac \<in> set (actions D)"
    using detype_dom_sel(4) detype_prob_sel(1) p2.res_aux by auto
  hence "ac_name (detype_ac ac) = n"
    using p2.resolve_action_schema_def index_by_eq_SomeD assms by metis
  hence "ac_name ac = n" using t_ac_name by simp
  thus ?thesis using that ac ac_in resolve_action_schema_def wf_DP(6) by simp
qed


lemma (in restr_problem2)
  assumes "d2.resolve_action_schema n = Some (detype_ac ac)" "ac \<in> set (actions D)"
  shows "resolve_action_schema n = Some ac"
proof -
  from assms have "ac_name (detype_ac ac) = n"
    by (metis d2.resolve_action_schema_def index_by_eq_SomeD)
  hence "ac_name ac = n" by (simp add: t_ac_name)
  thus ?thesis
    by (simp add: assms(2) resolve_action_schema_def wf_DP(6))
qed



subsubsection \<open> Semantics \<close>

text \<open>
A static predicate can never be modified by actions, since it isn't in their effects.
- prove type preds not in effects
  - effects wf w.r.t. old domain
  - atom wf ==> predicate exists
\<close>

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

(* unnecessary because of wf_plan_action_simple *)
lemma (in wf_ast_problem) "wf_plan_action \<pi> \<Longrightarrow> wf_effect objT (effect (resolve_instantiate \<pi>))"
  by (cases \<pi>; simp split:option.splits add: wf_effect_inst_alt)
  (* apply (cases \<pi>)
  apply (simp split: option.splits)
  using wf_effect_inst_alt by simp *)

context restr_problem2
begin

lemma t_params_match:
  assumes "action_params_match ac args"
  shows "p2.action_params_match (detype_ac ac) args"
proof -
  from assms have len: "length (ac_params ac) = length args"
    by (simp add: list_all2_lengthD action_params_match_def)
  hence len2: "length (ac_params (detype_ac ac)) = length args"
    by (cases ac; simp; metis length_map detype_ents_def)

  have "p2.is_obj_of_type (args ! i) (snd (ac_params (detype_ac ac) ! i))"
    if "i < length args" for i
  proof -
    have "is_obj_of_type (args ! i) (snd ((ac_params ac) ! i))"
      using that assms len
      by (simp add: action_params_match_def list_all2_conv_all_nth)
    hence "objT (args ! i) \<noteq> None" using is_obj_of_type_def by (metis option.simps(4))
    hence "p2.is_obj_of_type (args ! i) \<omega>" using t_objT_Some p2.is_obj_of_type_def by simp
    thus ?thesis using that len2 by (simp add: detype_ac_alt detype_ent_alt detype_ents_def)
  qed
  thus "?thesis"
    by (simp add: len2 list_all2_conv_all_nth p2.action_params_match_def)
qed

(* TODO clean this up, if possible *)
lemma detyped_planaction_enabled_iff:
  assumes "wf_world_model s"
  shows "plan_action_enabled \<pi> s \<longleftrightarrow> p2.plan_action_enabled \<pi> (s \<union> sf_substate)"
proof -
  obtain n args where pi: "\<pi> = PAction n args" by (cases \<pi>; simp)
  let ?pi = "PAction n args"

  have s_basic: "wm_basic s"
    using assms wf_world_model_def wf_fmla_atom_alt wm_basic_def by metis

  {
    assume assm: "plan_action_enabled ?pi s"
    hence wf: "wf_plan_action ?pi" and entail: "s \<^sup>c\<TTurnstile>\<^sub>= precondition (resolve_instantiate ?pi)"
      using plan_action_enabled_def by simp_all

    (* actions *)
    from wf obtain ac where res: "resolve_action_schema n = Some ac"
      by fastforce
    hence res2: "d2.resolve_action_schema n = Some (detype_ac ac)"
      by (rule t_resinst)

    (* parameter mappings *)
    let ?pre_map = "(map_formula \<circ> map_atom) (ac_tsubst (parameters ac) args)"
    let ?pre_map2 = "(map_formula \<circ> map_atom) (ac_tsubst (parameters (detype_ac ac)) args)"
    have "map fst (parameters (detype_ac ac)) = map fst (parameters ac)"
      by (cases ac; simp add: t_ents_names)
    hence premaps: "?pre_map2 = ?pre_map" using ac_tsubst_def by simp

    (* "left" side: from wf_plan_action \<pi> show p2.wf_plan_action \<pi> *)
    from wf res have match: "action_params_match ac args" by simp
    hence "p2.action_params_match (detype_ac ac) args"
      using t_params_match by simp
    with res2 have wf2: "p2.wf_plan_action ?pi"
      using p2.wf_plan_action_simple detype_prob_sel(1) by fastforce

    (* "middle": from action_params_match ac args show s \<union> sf_substate satisfy the param precond of the instantiated action.*)
    from match have entail_typ: "sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (param_precond (ac_params ac))"
      using params_match_iff_type_precond res res_aux wf_D(7) by simp
    (* Since init doesn't interfere with the type predicates,
       we can add it to sf_substate here and still satisfy them. *)
    from assms have "s \<inter> Atom ` atoms (?pre_map (param_precond (ac_params ac))) = {}"
      using wf_wm_disj_param_pre by simp
    with entail_typ have entail_L: "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (param_precond (ac_params ac))"
      using entail_adds_irrelevant[OF sf_basic s_basic] Un_commute by metis
    
    (* "right" side: show s satisfies action precond \<Longrightarrow> s \<union> sf_substate satisfies instantiated action precond in P2 *)
    have entail_pre: "s \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (ac_pre ac)"
      using entail res instantiate_action_schema_alt by force
    (* Since sf_substate doesn't interfere with the precondition,
       we can add it to init here and still satisfy it. *)
    have "wf_action_schema ac" using res wf_D(7) res_aux by simp
    hence "wf_fmla (ty_term (map_of (ac_params ac)) constT) (ac_pre ac)"
      using wf_action_schema_alt by simp
    hence "sf_substate \<inter> Atom ` atoms (?pre_map (ac_pre ac)) = {}"
      using sf_disj_wf_fmla by blast
    with entail_pre have entail_R: "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (ac_pre ac)"
      using entail_adds_irrelevant[OF s_basic sf_basic] by simp

    (* putting it together *)
    from entail_L entail_R have entail_map2:
      "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map2 ((param_precond (ac_params ac)) \<^bold>\<and> (ac_pre ac))"
      unfolding entailment_def using premaps by simp
    hence entail2: "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= precondition (p2.resolve_instantiate ?pi)"
      using entail_map2 res2 detype_prob_sel(1) by (simp add: detype_ac_alt p2.instantiate_action_schema_alt)
    with wf2 have "p2.plan_action_enabled ?pi (s \<union> sf_substate)"
      by (simp add: p2.plan_action_enabled_def)
  }
  moreover {
    assume "p2.plan_action_enabled ?pi (s \<union> sf_substate)"
    hence wf2: "p2.wf_plan_action ?pi" and entail2: "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= precondition (p2.resolve_instantiate ?pi)"
      using p2.plan_action_enabled_def by simp_all

    (* actions *)
    from wf2 obtain ac2 where res2: "p2.resolve_action_schema n = Some ac2"
      using p2.wf_pa_refs_ac by metis
    then obtain ac where ac[simp]: "ac2 = detype_ac ac" and ac_in: "ac \<in> set (actions D)"
      and res: "resolve_action_schema n = Some ac" by (metis t_resinst_inv)

    (* parameter mappings *)
    let ?pre_map2 = "(map_formula \<circ> map_atom) (ac_tsubst (ac_params ac2) args)"
    let ?pre_map = "(map_formula \<circ> map_atom) (ac_tsubst (ac_params ac) args)"
    have t_param_names: "map fst (parameters ac) = map fst (parameters (detype_ac ac))"
      by (cases ac; simp add: t_ents_names)
    hence premaps: "?pre_map = ?pre_map2" using ac_tsubst_def by simp

    (* "right" side *)
    have "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map2 (ac_pre ac2)"
      using entail2 res2 instantiate_action_schema_alt by force
    hence entail2: "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (param_precond (ac_params ac)) \<^bold>\<and> ?pre_map (ac_pre ac)"
      using detype_ac_alt premaps by force
    hence entail_a: "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (ac_pre ac)"
      using entailment_def entail_and by blast
    (* Since sf_substate doesn't interfere with the precondition,
       we can remove it from init here and still satisfy it. *)
    from ac_in have wf_ac: "wf_action_schema ac" using wf_D(7) by simp
    hence "wf_fmla (ty_term (map_of (ac_params ac)) constT) (ac_pre ac)"
      using wf_action_schema_alt by simp
    hence "sf_substate \<inter> Atom ` atoms (?pre_map (ac_pre ac)) = {}"
      using sf_disj_wf_fmla by simp
    with entail_a have "s \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (ac_pre ac)"
      using entail_adds_irrelevant[OF s_basic sf_basic] by simp
    hence entail: "s \<^sup>c\<TTurnstile>\<^sub>= precondition (resolve_instantiate ?pi)"
      using res instantiate_action_schema_alt by simp

    (* "middle" *)
    from wf2 res2 have match2: "p2.action_params_match ac2 args" by simp
    (* Since init doesn't interfere with the type predicates,
       we can remove it from i2 here and still satisfy them. *)
    have "\<forall>\<phi> \<in> s. wf_fmla_atom objT \<phi>"
      using assms wf_fmla_atom_alt wf_world_model_def by simp
    from assms have "s \<inter> Atom ` atoms (?pre_map (param_precond (ac_params ac))) = {}"
      using wf_wm_disj_param_pre by simp
    moreover from entail2 have "s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (param_precond (ac_params ac))"
      using entailment_def entail_and by blast
    ultimately have entail_typ: "sf_substate \<^sup>c\<TTurnstile>\<^sub>= ?pre_map (param_precond (ac_params ac))"
      using entail_adds_irrelevant[OF sf_basic s_basic] by (simp add: Set.Un_commute)

    (* "left" side *)
    hence "length (ac_params ac2) = length args"
      using match2 p2.action_params_match_def by (simp add: list_all2_lengthD)
    moreover have "length (ac_params ac) = length (ac_params (detype_ac ac))"
      using t_param_names map_eq_imp_length_eq by blast (*weird way to prove this*)
    ultimately have "length (ac_params ac) = length args"
      using detype_ac_alt detype_ents_def by simp
    hence "action_params_match ac args"
      using params_match_iff_type_precond[OF wf_ac] entail_typ by simp
    with res have wf: "wf_plan_action ?pi" using wf_plan_action_simple by fastforce

    from entail wf have "plan_action_enabled ?pi s"
      by (simp add: plan_action_enabled_def)
  }
  ultimately show ?thesis using pi by auto
qed

abbreviation "states_match s s' \<equiv> wf_world_model s \<and> s \<union> sf_substate = s'"

(* wf_execute has plan_action_enabled as assumption, and not the weaker (but still sufficient?)
  wf_plan_action *)
lemma match_state_step:
  assumes "states_match s s'" "execute_plan_action \<pi> s = t" "plan_action_enabled \<pi> s"
  shows "states_match t (p2.execute_plan_action \<pi> s')"
proof -
  obtain n args where pi: "\<pi> = PAction n args" by (cases \<pi>) simp
  then obtain ac where res: "resolve_action_schema n = Some ac"
    using assms(3) plan_action_enabled_def by fastforce
  hence 1: "effect (resolve_instantiate \<pi>) = map_ast_effect (ac_tsubst (ac_params ac) args) (ac_eff ac)"
    using pi instantiate_action_schema_alt by simp

  from pi obtain ac2 where res2: "p2.resolve_action_schema n = Some ac2" and t_ac: "ac2 = detype_ac ac"
    using res t_resinst detype_prob_sel(1) by simp
  hence 2: "effect (p2.resolve_instantiate \<pi>) = map_ast_effect (ac_tsubst (ac_params ac2) args) (ac_eff ac2)"
    using pi instantiate_action_schema_alt by simp

  from t_ac have "map fst (ac_params ac) = map fst (ac_params ac2)" using ast_domain.detype_ac_alt
    by (simp add: t_ents_names)
  moreover from t_ac have "ac_eff ac = ac_eff ac2" using detype_ac_alt by simp
  ultimately have effeq: "effect (resolve_instantiate \<pi>) = effect (p2.resolve_instantiate \<pi>)"
    using ac_tsubst_def 1 2 by force

  from res have "wf_action_schema ac"
    using res_aux wf_D(7) by simp
  with assms(3) have "wf_ground_action (resolve_instantiate \<pi>)"
    using wf_instantiate_action_schema pi res by (simp add: plan_action_enabled_def)
  hence "wf_effect objT (effect (resolve_instantiate \<pi>))"
    by (simp add: wf_ground_action_alt)
  with sf_disj_wf_eff[OF this, where f = id] have
    "sf_substate \<inter> set (adds (effect (resolve_instantiate \<pi>))) = {}"
    "sf_substate \<inter> set (dels (effect (resolve_instantiate \<pi>))) = {}"
    by (simp_all add: ast_effect.map_id)

  hence "apply_effect (effect (resolve_instantiate \<pi>)) (s \<union> sf_substate) =
    apply_effect (effect (resolve_instantiate \<pi>)) s \<union> sf_substate"
    using 1 apply_effect_alt sf_disj_wf_wm by auto
  hence "p2.execute_plan_action \<pi> s' = execute_plan_action \<pi> s \<union> sf_substate"
    using effeq execute_plan_action_def
    using p2.execute_plan_action_def assms(1) by simp
  moreover have "wf_world_model (execute_plan_action \<pi> s)" using wf_execute assms by auto
  ultimately show ?thesis using assms(2) by simp
qed

lemma goal_sem:
  assumes "wm_basic s"
  shows "s \<^sup>c\<TTurnstile>\<^sub>= goal P \<longleftrightarrow> s \<union> sf_substate \<^sup>c\<TTurnstile>\<^sub>= goal P2"
proof -  
  have "goal P2 = goal P" using detype_prob_sel(4) .
  hence 1: "s \<^sup>c\<TTurnstile>\<^sub>= goal P \<longleftrightarrow> s \<^sup>c\<TTurnstile>\<^sub>= goal P2" by simp
  have c3: "sf_substate \<inter> Atom ` atoms (goal P2) = {}"
    using detype_prob_sel(4) fmla_map_id sf_disj_wf_fmla[where f = id] wf_P(5) by metis
  note entail_adds_irrelevant[OF assms sf_basic c3]
  with 1 show ?thesis by simp
qed
lemma match_goal:
  assumes "states_match s s'"
  shows "s \<^sup>c\<TTurnstile>\<^sub>= goal P \<longleftrightarrow> s' \<^sup>c\<TTurnstile>\<^sub>= goal P2"
  using goal_sem assms wm_basic_def wf_world_model_def wf_fmla_atom_alt by metis

lemma match_valid_plan_from:
  assumes "states_match s s'" "valid_plan_from s \<pi>s"
  shows "p2.valid_plan_from s' \<pi>s"
using assms proof (induction \<pi>s arbitrary: s s')
  case Nil
  hence "s \<^sup>c\<TTurnstile>\<^sub>= goal P"
    using valid_plan_from_def by simp
  hence "s' \<^sup>c\<TTurnstile>\<^sub>= goal P2" using assms match_goal Nil.prems by simp
  thus ?case using p2.valid_plan_from_def by auto
next
  case (Cons p ps)
  let ?t = "execute_plan_action p s"
  let ?t' = "p2.execute_plan_action p s'"
  from Cons have enab1: "plan_action_enabled p s" and valid1: "valid_plan_from ?t ps"
    using valid_plan_from_def plan_action_path_Cons by auto
  from enab1 have enab2: "p2.plan_action_enabled p s'"
    using detyped_planaction_enabled_iff assms(1) Cons.prems by simp
  
  have "states_match ?t ?t'"
    using assms(1) enab1 match_state_step Cons.prems by blast
  hence "p2.valid_plan_from ?t' ps"
    using Cons.IH[OF _ valid1] by simp
  with enab2 show ?case using p2.valid_plan_from_def plan_action_path_Cons by simp
qed

lemma match_valid_plan:
  assumes "valid_plan \<pi>s" shows "p2.valid_plan \<pi>s"
proof -
  have "states_match I p2.I"
    using ast_problem.I_def detype_prob_sel(3) wf_I by auto
  thus ?thesis
  using assms match_valid_plan_from ast_problem.valid_plan_def by metis
qed

(* p2.valid_plan \<pi>s \<Longrightarrow> valid_plan \<pi>s *)


abbreviation reachable_prop :: "world_model \<Rightarrow> bool" where
  "reachable_prop s' \<equiv> \<exists>s. states_match s s'"
abbreviation (input) "RP \<equiv> reachable_prop"

lemma rp_props:
  assumes "RP M"
  shows
    "p2.wf_world_model M"
    "\<forall>x t. type_atom x t \<in> M \<longleftrightarrow> type_atom x t \<in> sf_substate"
    "wf_world_model (M - sf_substate)"
proof -
  from assms show "p2.wf_world_model M" using t_wm_wf
    using detype_prob_sel(1) p2.wf_world_model_def restr_problem2.super_facts_wf restr_problem2_axioms by auto
  from assms show "\<forall>x t. type_atom x t \<in> M \<longleftrightarrow> type_atom x t \<in> sf_substate"
    using wf_wm_no_typeatms by force
  from assms show "wf_world_model (M - sf_substate)"
    by (metis (no_types, lifting) Diff_cancel Int_left_commute Un_Diff Un_Diff_Int Un_Int_eq(4) inf_sup_absorb sf_disj_wf_wm)
qed

lemma rp_init: "RP (set (init P2))"
proof -
  have "set (init P2) = set (init P) \<union> sf_substate"
    using detype_prob_sel(3) by auto
  thus ?thesis using wf_P(4) by auto
qed

lemma rp_sf: "RP (sf_substate)"
  using wf_world_model_def by auto

lemma rp_enabled_iff:
  assumes "RP M"
  shows "plan_action_enabled \<pi> (M - sf_substate) \<longleftrightarrow> p2.plan_action_enabled \<pi> M"
  using assms detyped_planaction_enabled_iff rp_props by auto

(* TODO: lots of duplication from match_state_step*)
lemma match_state_step':
  assumes "states_match s s'" "p2.execute_plan_action \<pi> s' = t'" "p2.plan_action_enabled \<pi> s'"
  shows "states_match (execute_plan_action \<pi> s) t'"
proof -
  obtain n args where pi: "\<pi> = PAction n args" by (cases \<pi>) simp
  then obtain ac' where res': "p2.resolve_action_schema n = Some ac'"
    using assms(3) p2.plan_action_enabled_def by fastforce
  then obtain ac where res: "resolve_action_schema n = Some ac" and t_ac: "detype_ac ac = ac'"
    using t_resinst_inv by metis
  hence 1: "effect (resolve_instantiate \<pi>) = map_ast_effect (ac_tsubst (ac_params ac) args) (ac_eff ac)"
    using pi instantiate_action_schema_alt by simp
  from res' have 2: "effect (p2.resolve_instantiate \<pi>) = map_ast_effect (ac_tsubst (ac_params ac') args) (ac_eff ac')"
    using pi instantiate_action_schema_alt by simp

  from t_ac have "map fst (ac_params ac) = map fst (ac_params ac')"
    using detype_ac_alt t_ents_names by (metis ast_action_schema.sel(2))
  moreover from t_ac have "ac_eff ac = ac_eff ac'" using detype_ac_alt by auto
  ultimately have effeq: "effect (resolve_instantiate \<pi>) = effect (p2.resolve_instantiate \<pi>)"
    using ac_tsubst_def 1 2 by force

  from assms(1,3) have enab: "plan_action_enabled \<pi> s"
    using detyped_planaction_enabled_iff by simp
  moreover from res have "wf_action_schema ac"
    using res_aux wf_D(7) by simp
  ultimately have "wf_ground_action (resolve_instantiate \<pi>)"
    using wf_instantiate_action_schema pi res by (simp add: plan_action_enabled_def)
  hence "wf_effect objT (effect (resolve_instantiate \<pi>))"
    by (simp add: wf_ground_action_alt)
  with sf_disj_wf_eff[OF this, where f = id] have
    "sf_substate \<inter> set (adds (effect (resolve_instantiate \<pi>))) = {}"
    "sf_substate \<inter> set (dels (effect (resolve_instantiate \<pi>))) = {}"
    by (simp_all add: ast_effect.map_id)

  hence "apply_effect (effect (resolve_instantiate \<pi>)) (s \<union> sf_substate) =
    apply_effect (effect (resolve_instantiate \<pi>)) s \<union> sf_substate"
    using 1 apply_effect_alt sf_disj_wf_wm by auto
  hence "p2.execute_plan_action \<pi> s' = execute_plan_action \<pi> s \<union> sf_substate"
    using effeq execute_plan_action_def
    using p2.execute_plan_action_def assms(1) by simp
  moreover have "wf_world_model (execute_plan_action \<pi> s)" using wf_execute enab assms(1) by auto
  ultimately show ?thesis using assms(2) by simp
qed

lemma match_valid_plan_from':
  assumes "states_match s s'" "p2.valid_plan_from s' \<pi>s"
  shows "valid_plan_from s \<pi>s"
using assms proof (induction \<pi>s arbitrary: s s')
  case Nil
  hence "s' \<^sup>c\<TTurnstile>\<^sub>= goal P2"
    using p2.valid_plan_from_def by simp
  hence "s \<^sup>c\<TTurnstile>\<^sub>= goal P" using assms match_goal Nil.prems by simp
  thus ?case using valid_plan_from_def by auto
next
  case (Cons p ps)
  let ?t = "execute_plan_action p s"
  let ?t' = "p2.execute_plan_action p s'"
  from Cons have enab2: "p2.plan_action_enabled p s'" and valid2: "p2.valid_plan_from ?t' ps"
    using p2.valid_plan_from_def p2.plan_action_path_Cons by simp_all
  from enab2 have enab1: "plan_action_enabled p s"
    using detyped_planaction_enabled_iff assms(1) Cons.prems by simp
  
  have "states_match ?t ?t'"
    using assms(1) enab2 match_state_step' Cons.prems by blast
  hence "valid_plan_from ?t ps"
    using Cons.IH[OF _ valid2] by simp
  with enab1 show ?case using valid_plan_from_def plan_action_path_Cons by simp
qed

lemma match_valid_plan':
  assumes "p2.valid_plan \<pi>s" shows "valid_plan \<pi>s"
proof -
  have "states_match I p2.I"
    using ast_problem.I_def detype_prob_sel(3) wf_I by auto
  thus ?thesis
    using assms match_valid_plan_from' ast_problem.valid_plan_def by metis
qed

(* putting it together: *)

theorem detyped_valid_iff:
  "valid_plan \<pi>s \<longleftrightarrow> p2.valid_plan \<pi>s"
  using match_valid_plan match_valid_plan' by blast

end
end