theory PDDL_Normalization
  imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    Utils Graph_Funs String_Shenanigans
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
                  \<and> (\<forall>a\<in>set (actions D). wf_action_params a)"


locale restr_domain = wf_ast_domain +
  assumes restrict_dom: restrict_dom

definition (in ast_problem) restrict_prob :: bool where
  "restrict_prob \<equiv> restrict_dom
    \<and> single_types (objects P)
    \<and> only_conj (goal P)"

locale restr_problem = wf_ast_problem +
  assumes restrict_prob: restrict_prob

sublocale restr_problem \<subseteq> restr_domain "D"
  apply unfold_locales
  using restrict_prob restrict_prob_def by simp

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

  fun type_atom :: "'a \<Rightarrow> name \<Rightarrow> 'a atom formula" where
    "type_atom x t = Atom (predAtm (pred_for_type t) [x])"

  fun type_precond :: "variable \<times> type \<Rightarrow> term atom formula" where
    "type_precond (v, (Either ts)) = \<^bold>\<Or> (map (type_atom (term.VAR v)) ts)"

  fun param_precond :: "(variable \<times> type) list \<Rightarrow> term atom formula" where
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
  "detype_ac (Action_Schema nam params pre eff) =
    Action_Schema nam (detype_ents params) (param_precond params \<^bold>\<and> pre) eff"

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

(* TODO remove remdups lmao *)
definition (in ast_problem) detype_prob :: "ast_problem" where
"detype_prob \<equiv> Problem
    detype_dom
    (detype_ents (objects P))
    (remdups (supertype_facts (consts D @ objects P) @ (init P)))
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
  apply unfold_locales .

locale ast_problem2 = ast_problem
sublocale ast_problem2 \<subseteq> p2: ast_problem P2 .
sublocale ast_problem2 \<subseteq> ast_domain2 D .

locale wf_ast_problem2 = wf_ast_problem
sublocale wf_ast_problem2 \<subseteq> p2 : ast_problem P2.
sublocale wf_ast_problem2 \<subseteq> ast_problem2 .
sublocale wf_ast_problem2 \<subseteq> wf_ast_domain2 D
  apply unfold_locales .

locale restr_problem2 = restr_problem
sublocale restr_problem2 \<subseteq> p2 : ast_problem P2 .
sublocale restr_problem2 \<subseteq> wf_ast_problem2
  apply unfold_locales .
sublocale restr_problem2 \<subseteq> restr_domain2 D
  apply unfold_locales .


text \<open> Locale stuff \<close>

  (* just restrict_dom unfolded *)
  lemma (in restr_domain) restr_D: "single_types (consts D)" "(\<forall>a\<in>set (actions D). wf_action_params a)"
    using restrict_dom restrict_dom_def by auto
  
  (* just restrict_prob unfolded *)
  lemma (in restr_problem) restr_P: "single_types (objects P)" "only_conj (goal P)"
    using restrict_prob restrict_prob_def by auto
  
  lemma (in restr_problem) single_t_objs: "single_types (consts D @ objects P)"
    using restr_D restr_P by auto

  (* wf_domain unfolded and split *)
  lemmas (in wf_ast_domain) wf_D = conj_split_7[OF wf_domain[unfolded wf_domain_def]]

  (* wf_problem unfolded and split, but omitting the first fact "wf_domain" *)
  lemmas (in wf_ast_problem) wf_P =
    conj_split_5[OF wf_problem[unfolded wf_problem_def, THEN conjunct2]]

  lemmas (in wf_ast_problem) wf_DP = wf_D wf_P

  lemma (in ast_domain) detype_dom_sel:
    "types D2 = []"
    "predicates D2 = type_preds @ detype_preds (predicates D)"
    "consts D2 = detype_ents (consts D)"
    "actions D2 = map detype_ac (actions D)"
    using detype_dom_def by simp_all

  lemma (in ast_problem) detype_prob_sel:
    "domain P2 = D2"
    "objects P2 = detype_ents (objects P)"
    "init P2 = remdups (supertype_facts (consts D @ objects P) @ (init P))"
    "goal P2 = goal P"
    using detype_prob_def by simp_all

text \<open> basic stuff \<close>

  lemma dist_pred: "distinct names \<longleftrightarrow> distinct (map Pred names)"
    by (meson distinct_map inj_onI predicate.inject)

  lemma (in wf_ast_problem) objT_Some: "(n, T) \<in> set (consts D @ objects P) \<longleftrightarrow> objT n = Some T"
  proof -
    have "distinct (map fst (consts D @ objects P))"
      using wf_P(1) by auto
    thus ?thesis using objT_alt
      by (metis map_of_eq_Some_iff)
  qed

  lemma (in wf_ast_problem) cnst_obj_ids_disj:
    "fst ` set (consts D) \<inter> fst ` set (objects P) = {}"
    using list.set_map wf_P(1) by auto

  lemma (in wf_ast_problem) objm_le_objT: "map_of (objects P) \<subseteq>\<^sub>m objT"
  proof -
    have "dom constT \<inter> dom (map_of (objects P)) = {}"
      using constT_def cnst_obj_ids_disj
      by (simp add: dom_map_of_conv_image_fst)
    thus ?thesis using objT_def
      by (simp add: map_add_comm map_le_iff_map_add_commute)  
  qed

  lemma type_decomp_1: "single_type T \<Longrightarrow> \<exists>t. T = Either [t]"
  apply (cases T)
  using Misc.list_decomp_1 by auto

text \<open> type system \<close>

context ast_domain
begin

  lemma (in -) wf_object: "ast_domain.wf_type d \<omega>"
    unfolding ast_domain.wf_type.simps by simp

  lemma tyterm_prop: "P (ty_term varT cnstT x) \<longleftrightarrow>
    (case x of term.VAR x' \<Rightarrow> P (varT x') |
               term.CONST x' \<Rightarrow> P (cnstT x'))"
    apply (split term.split)
    by simp

  (* TODO: improve this to _eq_Some_iff *)
  lemma tyterm_elem: "(ty_term (map_of varT) (map_of cnstT) x \<noteq> None)
    \<longleftrightarrow> (case x of term.VAR x' \<Rightarrow> x' \<in> fst ` set varT |
                   term.CONST x' \<Rightarrow> x' \<in> fst ` set cnstT)"
    apply (split term.split)
    using tyterm_prop by (simp add: map_of_eq_None_iff)

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
    "distinct (map pred type_preds)" (is "distinct ?tp_ids")
    using pred_for_type_dis type_preds_ids by force

text \<open> detyped preds \<close>

  lemma preds_detyped:
    "\<forall>p \<in> set (predicates D2). \<forall>T \<in> set (argTs p). T = \<omega>"
    using type_preds_def detype_preds_def detype_dom_sel(2) by auto

  lemma dt_pred_id: "pred (detype_pred pd) = pred pd" by simp

  lemma dt_preds_ids:
    "map pred (detype_preds ps) = map pred ps"
    using dt_pred_id detype_preds_def by simp

  lemma type_pred_notin: "pred_for_type t \<notin> pred ` set (predicates D)"
  proof -
    have "predicate.name (pred_for_type t) \<notin> set pred_names"
      using safe_prefix_correct predicate.sel pred_for_type_def by presburger
    thus ?thesis by force
  qed

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
    apply (cases p) using preds_detyped wf_object by auto

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

  lemma (in ast_problem2) t_cnsts_objs_names: "map fst (consts D @ objects P)
    = map fst (detype_ents (consts D) @ detype_ents (objects P))"
    using t_ents_names by (metis map_append)

  lemma (in wf_ast_problem2) t_objm_le_objT:
    "map_of (objects P2) \<subseteq>\<^sub>m p2.objT"
  proof -
    have "distinct (map fst (consts D @ objects P))" using wf_P(1) by auto
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
    have "objT c \<noteq> None \<longleftrightarrow> c \<in> fst ` set (consts D @ objects P)" using t_cnsts_objs_names
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
    using assms apply (induction e)
    apply (metis t_entT_Some ty_term.simps(1))
    apply (metis t_entT_Some ty_term.simps(2))
    done

  lemma t_tyt_None:
    assumes "ty_term (map_of vars) (map_of cnsts) e = None"
    shows "ty_term (map_of (detype_ents vars)) (map_of (detype_ents cnsts)) e = None"
    using assms apply (induction e)
    apply (metis t_entT_None ty_term.simps(1))
    apply (metis t_entT_None ty_term.simps(2))
    done

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
    from predAtm this have 1: "list_all2 (is_of_type tyt) params Ts" by simp

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

  lemma wf_effect_alt:
    "wf_effect tyt \<epsilon> \<longleftrightarrow>
       (\<forall>ae\<in>set (adds \<epsilon>). wf_fmla_atom tyt ae)
       \<and> (\<forall>de\<in>set (dels \<epsilon>).  wf_fmla_atom tyt de)"
    apply (cases \<epsilon>) by simp

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

  abbreviation "ac_name \<equiv> ast_action_schema.name"
  abbreviation "ac_params \<equiv> ast_action_schema.parameters"
  abbreviation "ac_pre \<equiv> ast_action_schema.precondition"
  abbreviation "ac_eff \<equiv> ast_action_schema.effect"

  (* TODO just manipulate lemma *)
  lemma detype_ac_alt:
    "detype_ac ac = Action_Schema
      (ac_name ac)
      (detype_ents (ac_params ac))
      (param_precond (ac_params ac) \<^bold>\<and> (ac_pre ac))
      (ac_eff ac)"
    apply (cases ac) by simp

  (* TODO just manipulate lemma *)
  lemma wf_ac_alt:
    "wf_action_schema a \<longleftrightarrow> (
      let
        tyt = ty_term (map_of (ac_params a)) constT
      in
        distinct (map fst (ac_params a))
      \<and> wf_fmla tyt (ac_pre a)
      \<and> wf_effect tyt (ac_eff a))"
    apply (cases a) by simp

  lemma ac_params_detyped:
    "\<forall>ac \<in> set (actions D2). \<forall>(n, T) \<in> set (ac_params ac). T = \<omega>"
    using detype_dom_def detype_ac_alt ents_detyped by fastforce

  lemma t_ac_name: "ac_name (detype_ac ac) = ac_name ac"
    by (simp add: detype_ac_alt)
  lemma t_acs_names: "map ac_name (map detype_ac acs) = map ac_name acs"
    by (simp add: t_ac_name)
  lemma (in wf_ast_domain) t_acs_dis:
    "distinct (map ac_name (map detype_ac (actions D)))"
    using t_acs_names wf_D by metis

  lemma (in ast_domain2) t_ac_tyt:
    assumes "ty_term (map_of (ac_params a)) constT x \<noteq> None"
    shows "ty_term (map_of (ac_params (detype_ac a))) d2.constT x = Some \<omega>"
    using assms detype_ac_alt detype_dom_def t_tyt_Some ast_domain.constT_def by auto

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
  lemma (in wf_ast_domain2) type_precond_wf: (* TODO simplify if possible *)
    assumes "wf_action_params a" "p \<in> set (ac_params a)"
    shows "d2.wf_fmla
      (ty_term (map_of (ac_params (detype_ac a))) cnstT)
      (type_precond p)"
  proof -
    (* type_precond.cases? *)
    obtain n ts where p: "p = (n, Either ts)" using type_precond.cases by blast
    let ?tyt = "ty_term (map_of (ac_params a)) cnstT"
    let ?tyt2 = "ty_term (map_of (ac_params (detype_ac a))) cnstT"
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
    (ty_term (map_of (ac_params (detype_ac a))) cnstT)
    (param_precond (ac_params a))"
  proof -
    let ?tyt2 = "ty_term (map_of (ac_params (detype_ac a))) cnstT"
    have "\<forall>p \<in> set (ac_params a). d2.wf_fmla ?tyt2 (type_precond p)"
      using type_precond_wf assms by simp
    hence "\<forall>\<phi> \<in> set (map type_precond (ac_params a)). d2.wf_fmla ?tyt2 \<phi>" by simp
    thus ?thesis using d2.bigand_wf param_precond.simps by metis
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

    from assms have "distinct (map fst (ac_params a))" using wfa wf_ac_alt by metis
    hence c1: "distinct (map fst (ac_params ?a2))" using t_ents_dis detype_ac_alt by auto

    from assms have "wf_fmla ?tyt (ac_pre a)" using wfa wf_ac_alt by metis
    hence c2b: "d2.wf_fmla ?tyt2 (ac_pre a)" using tyt_om t_fmla_wf by blast
    have "wf_action_params a" using restr_D(2) assms by simp
    note c2a = t_param_precond_wf[OF this]
    from c2a c2b have c2: "d2.wf_fmla ?tyt2 (ac_pre ?a2)" by (simp add: detype_ac_alt)

    from assms have wfeff: "wf_effect ?tyt (ac_eff a)" using wfa wf_ac_alt by metis
    hence "d2.wf_effect ?tyt2 (ac_eff a)" by (rule t_eff_wf[OF tyt_om])
    hence c3: "d2.wf_effect ?tyt2 (ac_eff ?a2)" using detype_ac_alt by simp

    from c1 c2 c3 show ?thesis using d2.wf_ac_alt by simp
  qed

  lemma (in restr_domain2) t_acs_wf:
    shows "(\<forall>a\<in>set (map detype_ac (actions D)). d2.wf_action_schema a)"
    using detype_dom_def wf_D t_ac_wf by simp

text \<open> supertype_facts (init) \<close> (* TODO maybe move elsewhere *)

  (* super simple because of remdups *)
  lemma (in restr_problem) t_init_dis: "distinct (init P2)"
    using detype_prob_sel by simp

  abbreviation (input) get_t :: "type \<Rightarrow> name" where
    "get_t T \<equiv> hd (primitives T)"
  lemma get_t_alt: "get_t (Either (t # ts)) = t" by simp

  lemma superfacts_for_cond:
    assumes "single_type T"
    shows "supertype_facts_for (n, T) =
      map (type_atom n) (supertypes_of (get_t T))"
    using assms type_decomp_1 supertype_facts_for.simps(1) by fastforce

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

  (* I could do "p2.wf_world_model (set (supertype_facts_for ent))"
     but it doesn't make it more readable imo. *)
  lemma (in restr_problem2) super_facts_for_wf:
    assumes "(n, T) \<in> set (consts D @ objects P)"
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
    shows "\<forall>\<phi> \<in> set (supertype_facts (consts D @ objects P)). d2.wf_fmla_atom p2.objT \<phi>"
    using super_facts_for_wf supertype_facts_def by auto

  lemma (in restr_problem2) t_init_wf:
    "p2.wf_world_model (set (init P2))"
  proof -
    have tyt: "\<forall>c. (objT c \<noteq> None) \<longrightarrow> (p2.objT c = Some \<omega>)" using t_objT_Some by simp
    have "\<forall>\<phi> \<in> set (init P). wf_fmla_atom objT \<phi>"
      using wf_P(4)[unfolded wf_world_model_def] .
    hence c1: "\<forall>\<phi> \<in> set (init P). d2.wf_fmla_atom p2.objT \<phi>"
      using t_fmla_atom_wf[OF tyt] by simp

    note c23 = super_facts_wf

    from c1 c23 show ?thesis
      using detype_prob_def supertype_facts_def p2.wf_world_model_def by auto
  qed

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

  lemma subtype_edge_swap:
    "subtype_edge = prod.swap"
  proof -
    have "\<And>a b. subtype_edge (a, b) = prod.swap (a, b)"
      by simp
    thus ?thesis by fast
  qed

  lemma subtype_rel_alt: "subtype_rel\<^sup>* = ((set (types D))\<^sup>*)\<inverse>"
  proof -
    have "subtype_rel = set (map prod.swap (types D))"
      using subtype_rel_def subtype_edge_swap by metis
    hence "subtype_rel = (set (types D))\<inverse>" by auto
    thus ?thesis by (simp add: rtrancl_converse)
  qed

  lemma of_type_iff_reach:
    shows "of_type (Either oT) (Either T) \<longleftrightarrow> (
      \<forall>ot \<in> set oT.
      \<exists>t \<in> set T.
        t \<in> set (supertypes_of ot))"
  proof -
    have "of_type (Either oT) (Either T) \<longleftrightarrow>
      set oT \<subseteq> ((set (types D))\<^sup>*)\<inverse> `` set T"
      using subtype_rel_alt of_type_def by simp
    also have "... \<longleftrightarrow>
      (\<forall>ot \<in> set oT. ot \<in> ((set (types D))\<^sup>*)\<inverse> `` set T)"
      by auto
    also have "... \<longleftrightarrow>
      (\<forall>ot \<in> set oT. \<exists>t. (ot, t) \<in> (set (types D))\<^sup>* \<and> t \<in> set T)"
      by auto
    finally show ?thesis using reachable_iff_in_star by metis
  qed

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

  lemma (in ast_problem) simple_obj_of_type_iff:
    assumes "objT n = Some (Either [ot])"
    shows  "is_obj_of_type n (Either T) \<longleftrightarrow>
        (\<exists>t \<in> set T.
      t \<in> set (supertypes_of ot))"
    using assms is_obj_of_type_def single_of_type_iff by auto
end

subsubsection \<open> Type Pred semantics \<close>

lemma (in ast_domain) wf_predatom_pred_listed:
  assumes "wf_pred_atom tyt (p, n)"
  shows "p \<in> pred ` set (predicates D)"
  using assms sig_None wf_pred_atom.simps
  by (metis option.simps(4))

(* what's the builtin way? *)
fun un_Atom :: "'a formula \<Rightarrow> 'a" where
  "un_Atom (Atom x) = x" |
  "un_Atom _ = undefined"
lemma "(predicate \<circ> un_Atom) (Atom (predAtm p args)) = p"
  by simp
abbreviation "unPredAtom x \<equiv> predicate (un_Atom x)"

lemma predatom_preds: "is_predAtom \<phi> \<Longrightarrow> fmla_preds \<phi> = {unPredAtom \<phi>}"
  using un_Atom.simps(1)
  by (metis atom.sel(1) fmla_preds_simps(1) is_predAtom.elims(2))

context ast_domain
begin

lemma wf_fmlaatom_pred_listed:
  assumes "wf_fmla_atom tyt \<phi>"
  shows "unPredAtom \<phi> \<in> pred ` set (predicates D)"
  using assms wf_predatom_pred_listed
  by (metis atom.sel(1) un_Atom.simps(1) wf_fmla_atom.elims(2))

lemma wf_fmla_preds_listed:
  assumes "wf_fmla tyt \<phi>"
  shows "fmla_preds \<phi> \<subseteq> pred ` set (predicates D)"
  using assms apply (induction \<phi>)
  using wf_predatom_pred_listed
       apply (metis bot.extremum fmla_preds_simps(1-2) insert_subset wf_atom.elims(2) wf_fmla.simps(1))
  by simp_all

lemma typeatom_disj_fmla_preds:
  assumes "wf_fmla tyt \<phi>"
  shows "fmla_preds (type_atom x t) \<inter> fmla_preds \<phi> = {}"
proof -
  from assms have "fmla_preds \<phi> \<subseteq> pred ` set (predicates D)"
    using wf_fmla_preds_listed by simp
  moreover have "unPredAtom (type_atom x t) \<notin> pred ` set (predicates D)"
    using type_pred_notin by simp
  ultimately show ?thesis using predatom_preds by auto
qed

end

context restr_problem2
begin

thm ast_domain.wf_effect.simps
thm valuation_iff_close_world

abbreviation "super_facts \<equiv> supertype_facts (consts D @ objects P)"
abbreviation "sf_substate \<equiv> set super_facts"
(* todo rename: substate affected by effect *)
abbreviation influence :: "'a ast_effect \<Rightarrow> 'a atom formula set" where
  "influence eff \<equiv> set (adds eff) \<union> set (dels eff)"

lemma superfactsfor_disj_fmla_preds:
  assumes "wf_fmla tyt \<phi>" "single_type T"
  shows "\<Union>(fmla_preds ` set (supertype_facts_for (x, T))) \<inter> fmla_preds \<phi> = {}"
  using assms superfacts_for_cond typeatom_disj_fmla_preds by fastforce

lemma superfacts_disj_fmla_preds:
  assumes "wf_fmla tyt \<phi>"
  shows "\<Union>(fmla_preds ` sf_substate) \<inter> fmla_preds \<phi> = {}"
  using assms single_t_objs superfactsfor_disj_fmla_preds supertype_facts_def by fastforce

lemma superfacts_disj_eff:
  assumes "wf_effect tyt eff"
  shows "\<Union>(fmla_preds ` sf_substate) \<inter> \<Union>(fmla_preds ` influence eff) = {}"
proof -
  have "\<forall> \<phi> \<in> influence eff. wf_fmla tyt \<phi>"
    using assms wf_effect_alt wf_fmla_atom_alt by blast
  thus ?thesis using assms superfacts_disj_fmla_preds by blast
qed

thm resolve_instantiate.simps
thm execute_plan_action_def
thm apply_effect.simps
thm instantiate_action_schema.simps
thm map_preserves_fmla_preds

lemma instantiate_ac_alt:
    "instantiate_action_schema ac args = (let
        tsubst = subst_term (the o (map_of (zip (map fst (ac_params ac)) args)))
      in
        Ground_Action
          ((map_formula o map_atom) tsubst (ac_pre ac))
          ((map_ast_effect) tsubst (ac_eff ac))
      )"
  by (cases ac) simp

lemma inst_ac_preserves_pre_preds:
  "fmla_preds (ac_pre ac) = fmla_preds (precondition (instantiate_action_schema ac args))"
proof -
  obtain m where "precondition (instantiate_action_schema ac args)
    = (map_formula o map_atom) m (ac_pre ac)"
    using instantiate_ac_alt by (metis ground_action.sel(1))
  thus ?thesis using map_preserves_fmla_preds by auto
qed
                  
lemma map_preserves_eff_preds:
  "\<Union>(fmla_preds ` influence eff) = \<Union>(fmla_preds ` influence (map_ast_effect f eff))"
proof -
  have 
    "map_ast_effect f eff = Effect
      ((map \<circ> map_formula \<circ> map_atom) f (adds eff))
      ((map \<circ> map_formula \<circ> map_atom) f (dels eff))"
    by (cases eff) simp
  thus ?thesis using map_preserves_fmla_preds by auto
qed

lemma inst_ac_preserves_eff_preds:
  "\<Union>(fmla_preds ` influence (ac_eff ac))
    = \<Union>(fmla_preds ` influence (effect (instantiate_action_schema ac args)))"
proof -
  obtain m where "effect (instantiate_action_schema ac args)
    = map_ast_effect m (ac_eff ac)"
    using instantiate_ac_alt by (metis ground_action.sel(2))
  thus ?thesis using map_preserves_eff_preds by simp
qed

thm wf_instantiate_action_schema

lemma (* I could have saved some time on the next two lol *)
  assumes "wf_action_schema ac" "action_params_match ac args"
  defines "eff_inst \<equiv> effect (instantiate_action_schema ac args)"
  shows "\<Union>(fmla_preds ` sf_substate) \<inter> \<Union>(fmla_preds ` influence eff_inst) = {}"
proof -
  have "wf_ground_action (instantiate_action_schema ac args)"
    using assms wf_instantiate_action_schema by simp
  hence "wf_effect objT eff_inst"
    by (metis eff_inst_def ground_action.collapse wf_ground_action.simps)
  thus ?thesis using superfacts_disj_eff by blast
qed

lemma superfacts_disj_inst_eff:
  assumes "wf_action_schema ac" "eff_inst = effect (instantiate_action_schema ac args)"
  shows "\<Union>(fmla_preds ` sf_substate) \<inter> \<Union>(fmla_preds ` influence eff_inst) = {}"
  using assms wf_ac_alt inst_ac_preserves_eff_preds superfacts_disj_eff by metis

lemma superfacts_disj_inst_pre:
  assumes "wf_action_schema ac" "pre_inst = precondition (instantiate_action_schema ac args)"
  shows "\<Union>(fmla_preds ` sf_substate) \<inter> fmla_preds pre_inst = {}"
  using assms wf_ac_alt inst_ac_preserves_pre_preds superfacts_disj_fmla_preds by metis


thm execute_ground_action_def
thm apply_effect.simps

definition "type_substate s \<equiv> {predAtm p xs | p xs t. p = pred_for_type t}"

lemma
  assumes "wf_effect tyt eff" "sf_substate \<subseteq> s"
  shows "sf_substate \<subseteq> (apply_effect eff s)"
  oops

lemma "wm_basic sf_substate"
proof -
  have "sf_substate \<subseteq> set (init P2)" using detype_prob_def by simp
  moreover have "wm_basic (set (init P2))" using wm_basic_def detype_prob_wf
    using p2.wf_P(4) p2.wf_fmla_atom_alt p2.wf_world_model_def by auto
  ultimately show ?thesis using wm_basic_def by blast
qed

  (* wf action \<rightarrow> wf effect \<rightarrow> wf_fmla_atom \<rightarrow> wf_pred_atom *)




value "type_atom x t \<notin> set (adds (ac_eff ac))"





lemma
  "sf_substate \<inter> set (adds (effect ac)) = {}"
  oops

lemma
  "sf_substate \<^sup>c\<TTurnstile>\<^sub>= S \<Longrightarrow> sf_substate \<^sup>c\<TTurnstile>\<^sub>= step"
  oops

end

text \<open>
A static predicate can never be modified by actions, since it isn't in their effects.
- prove type preds not in effects
  - effects wf w.r.t. old domain
  - atom wf ==> predicate exists
\<close>

lemma valuation_upd_aux1:
  assumes "is_predAtm a"
  shows "valuation (insert (Atom a) M) x = ((valuation M)(a := True)) x"
proof -
  have "valuation (insert (Atom a) M) x \<longleftrightarrow>
    (case x of predAtm p xs \<Rightarrow> x = a \<or> Atom (predAtm p xs) \<in> M | Eq a b \<Rightarrow> a = b)"
    by (cases x) (simp_all add: valuation_def)
  also have "... \<longleftrightarrow> ((x = a) \<or> (case x of predAtm p xs \<Rightarrow> Atom (predAtm p xs) \<in> M | Eq a b \<Rightarrow> a = b))"
    using assms by (cases x) auto
  also have "... \<longleftrightarrow> ((valuation M)(a := True)) x" by (simp add: valuation_def)
  ultimately show ?thesis by simp
qed

lemma valuation_upd_aux2:
  assumes "is_predAtm a"
  shows "valuation (M - {Atom a}) x = ((valuation M)(a := False)) x"
proof -
  have "valuation (M - {Atom a}) x \<longleftrightarrow>
    (case x of predAtm p xs \<Rightarrow> x \<noteq> a \<and> Atom (predAtm p xs) \<in> M | Eq a b \<Rightarrow> a = b)"
    by (cases x) (auto simp add: valuation_def)
  also have "... \<longleftrightarrow> ((x \<noteq> a) \<and> (case x of predAtm p xs \<Rightarrow> Atom (predAtm p xs) \<in> M | Eq a b \<Rightarrow> a = b))"
    using assms by (cases x) auto
  also have "... \<longleftrightarrow> ((valuation M)(a := False)) x" by (simp add: valuation_def)
  ultimately show ?thesis by simp
qed

lemma valuation_upd1:
  assumes "is_predAtm a"
  shows "valuation (M \<union> {Atom a}) = (valuation M)(a := True)"
  using assms valuation_upd_aux1 by auto

lemma valuation_upd2:
  assumes "is_predAtm a"
  shows "valuation (M - {Atom a}) = (valuation M)(a := False)"
  using assms valuation_upd_aux2 by auto

context restr_problem2
begin 

thm wf_fmla_atom_alt

(* Yes, lots of copy paste between the next two lemmas. *)
lemma valuation_adds_upd:
  assumes "\<forall>a \<in> set ads. is_predAtom a"
  shows "valuation (M \<union> set ads) = foldr (\<lambda>a v. v(un_Atom a := True)) ads (valuation M)"
using assms proof (induction ads arbitrary: M)
  case (Cons ad ads)
  hence atm: "is_predAtom ad" by simp
  then obtain x where x: "Atom x = ad"
    by (metis is_predAtom.elims(2))
  hence un_x: "x = un_Atom ad" by auto
  from x have pax: "is_predAtm x" using atm is_predAtm_def
    by (metis is_predAtom.elims(2) un_Atom.simps(1))
  let ?upd = "\<lambda>a v. v(un_Atom a := True)"

  have "valuation (M \<union> set (ad # ads)) = valuation (M \<union> set ads \<union> {Atom x})"
    using x by simp
  also have "... = (valuation (M \<union> set ads))(x := True)"
    using valuation_upd1 pax by metis
  also have "... = (valuation (M \<union> set ads))(un_Atom ad := True)"
    using un_x by simp
  also have "... = (foldr ?upd ads (valuation M))(un_Atom ad := True)"
    using Cons by fastforce
  also have "... = foldr ?upd (ad#ads) (valuation M)" by simp
  ultimately show ?case by metis
qed simp

lemma valuation_dels_upd:
  assumes "\<forall>a \<in> set ads. is_predAtom a"
  shows "valuation (M - set ads) = foldr (\<lambda>a v. v(un_Atom a := False)) ads (valuation M)"
using assms proof (induction ads arbitrary: M)
  case (Cons ad ads)
  hence atm: "is_predAtom ad" by simp
  then obtain x where x: "Atom x = ad"
    by (metis is_predAtom.elims(2))
  hence un_x: "x = un_Atom ad" by auto
  from x have pax: "is_predAtm x" using atm is_predAtm_def
    by (metis is_predAtom.elims(2) un_Atom.simps(1))
  let ?upd = "\<lambda>a v. v(un_Atom a := False)"

  have "valuation (M - set (ad # ads)) = valuation (M - set ads - {Atom x})"
    using x by (metis Diff_insert list.simps(15))
  also have "... = (valuation (M - set ads))(x := False)"
    using valuation_upd2 pax by metis
  also have "... = (valuation (M - set ads))(un_Atom ad := False)"
    using un_x by simp
  also have "... = (foldr ?upd ads (valuation M))(un_Atom ad := False)"
    using Cons by fastforce
  also have "... = foldr ?upd (ad#ads) (valuation M)" by simp
  ultimately show ?case by metis
qed simp

definition pred_atoms :: "'ent atom formula \<Rightarrow> 'ent atom set" where
  "pred_atoms F = {predAtm p xs | p xs. predAtm p xs \<in> atoms F}"
lemma "pred_atoms F \<subseteq> atoms F" using pred_atoms_def
  by (smt (verit, best) mem_Collect_eq subsetI)
end

(* ---------------------- Future Milestones ------------------------- *)

context restr_problem2
begin



lemma t_init_substate: "set (init P2) = sf_substate \<union> set (init P)" using detype_prob_def supertype_facts_def by auto

lemma t_init_disj: "sf_substate \<inter> set (init P) = {}" sorry

lemma t_substate_static: "sf_substate \<subseteq> s \<Longrightarrow> sf_substate \<subseteq> p2.execute_plan_action \<pi> s"
  oops


(* left direction not true, use \uplus instead *)
lemma t_exec_equiv: "execute_plan_action \<pi> s = s' \<longleftrightarrow> p2.execute_plan_action \<pi> (sf_substate \<union> s) = sf_substate \<union> s'"
  oops


lemma "s \<inter> t = {} \<Longrightarrow> s' = s \<longleftrightarrow> (s' \<inter> t = {} \<and> s' \<union> t = s \<union> t)" by auto

lemma x3:
  assumes "sf_substate \<inter> s' = {}"
  shows "plan_action_path (set (init P)) \<pi>s s' \<longleftrightarrow> p2.plan_action_path (set (init P2)) \<pi>s (sf_substate \<union> s')"
  using assms
proof (induction \<pi>s arbitrary: s')
  case Nil
  have "plan_action_path (set (init P)) Nil s' \<longleftrightarrow> s' = set (init P)" by simp
  also have "... \<longleftrightarrow> s' \<union> sf_substate = set (init P) \<union> sf_substate" using t_init_disj sorry
  have "\<And>s''. plan_action_path (set (init P2)) Nil s'' \<longleftrightarrow> s'' = set (init P2) \<union> sf_substate"
    using t_init_substate by force
  oops

lemma x2: "s \<^sup>c\<TTurnstile>\<^sub>= goal P \<longleftrightarrow> sf_substate \<union> s \<^sup>c\<TTurnstile>\<^sub>= goal P2"
  oops

lemma "valid_plan \<pi>s \<Longrightarrow> p2.valid_plan \<pi>s"
  apply (induction \<pi>s)
  oops


end
end