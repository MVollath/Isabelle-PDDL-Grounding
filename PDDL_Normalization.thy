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
  
  abbreviation pred_for_type :: "name \<Rightarrow> predicate" where
    "pred_for_type t \<equiv> Pred (safe_prefix pred_names @ t)"
  
  definition type_preds :: "predicate_decl list" where
    "type_preds \<equiv> map ((\<lambda>p. PredDecl p [\<omega>]) \<circ> pred_for_type) type_names"

  abbreviation supertypes_of :: "name \<Rightarrow> name list" where
    "supertypes_of \<equiv> reachable_nodes (types D)"

  definition supertype_preds :: "name \<Rightarrow> predicate list" where
    "supertype_preds t \<equiv> map pred_for_type (supertypes_of t)"
  
  text \<open>This only works for single types on purpose.\<close>
  fun supertype_facts_for :: "(object \<times> type) \<Rightarrow> object atom formula list" where
    "supertype_facts_for (n, Either [t]) =
      map (Atom \<circ> (\<lambda>p. predAtm p [n])) (supertype_preds t)" |
    "supertype_facts_for (n, _) = undefined"

  fun type_cond :: "variable \<Rightarrow> name \<Rightarrow> term atom formula" where
    "type_cond v t = Atom (predAtm (pred_for_type t) [term.VAR v])"
  fun type_precond :: "variable \<times> type \<Rightarrow> term atom formula" where
    "type_precond (v, (Either ts)) = disj_fmlas (map (type_cond v) ts)"

(**) lemma xd: "type_precond (v, (Either ts))
  = disj_fmlas (map ((\<lambda>p. Atom (predAtm p [term.VAR v])) \<circ> pred_for_type) ts)"
  by (smt (verit) ast_domain.type_precond.simps fun_comp_eq_conv type_cond.simps)

(**) lemma xd2: "type_precond (v, (Either ts))
  = disj_fmlas (map (Atom \<circ>(\<lambda>p. predAtm p [term.VAR v]) \<circ> pred_for_type) ts)"
  using xd fun_comp_eq_conv by fastforce

(*  fun type_conds :: "type \<Rightarrow> predicate list" where
    "type_conds T = map pred_for_type (primitives T)"
  
  fun type_precond :: "(variable \<times> type) \<Rightarrow> term atom formula" where
    "type_precond (v, T) =
      disj_fmlas (map (Atom \<circ> (\<lambda>p. predAtm p [term.VAR v])) (type_conds T))" *)
  
  fun param_precond :: "(variable \<times> type) list \<Rightarrow> term atom formula" where
    "param_precond params = conj_fmlas (map type_precond params)"

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

  definition supertype_facts :: "(object \<times> type) list \<Rightarrow> object atom formula list" where
    "supertype_facts objs \<equiv> concat (map supertype_facts_for objs)"
end

definition (in ast_problem) detype_prob :: "ast_problem" where
"detype_prob \<equiv> Problem
    detype_dom
    (detype_ents (objects P))
    (supertype_facts (objects P) @ supertype_facts (consts D) @ (init P))
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

text \<open> basic stuff \<close>

  lemma (in -) dist_pred: "distinct names \<longleftrightarrow> distinct (map Pred names)"
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

text \<open> type system \<close>

context ast_domain
begin

  lemma (in -) wf_object: "ast_domain.wf_type d \<omega>"
    unfolding ast_domain.wf_type.simps by simp

  lemma subtype_edge_swap:
    "subtype_edge = prod.swap"
  proof -
    have "\<And>a b. subtype_edge (a, b) = prod.swap (a, b)"
      by simp
    thus ?thesis by fast
  qed

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

  lemma pred_for_type_inj: "inj pred_for_type" using inj_def by auto

  lemma pred_for_type_dis:
    assumes "distinct ts"
    shows "distinct (map pred_for_type ts)"
    using assms pred_for_type_inj by (rule map_inj_dis)

text \<open> type_preds \<close>

  lemma type_preds_dis:
    "distinct (map pred type_preds)" (is "distinct ?tp_ids")
    using pred_for_type_dis type_preds_ids by force

text \<open> supertype preds \<close>

text \<open> supertype facts \<close>

text \<open> type conds/preconds \<close>

text \<open> detyped preds \<close>

  lemma preds_detyped:
    "\<forall>p \<in> set (predicates D2). \<forall>T \<in> set (argTs p). T = \<omega>"
    using type_preds_def detype_preds_def detype_dom_def by auto

  lemma dt_pred_id: "pred (detype_pred pd) = pred pd" by simp

  lemma dt_preds_ids:
    "map pred (detype_preds ps) = map pred ps"
    using dt_pred_id detype_preds_def by simp

  lemma type_pred_notin: "pred_for_type t \<notin> pred ` set (predicates D)"
  proof -
    have "predicate.name (pred_for_type t) \<notin> set pred_names"
      using safe_prefix_correct predicate.sel by presburger
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
    thus ?thesis using detype_dom_def by simp
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

  lemma (in wf_ast_domain2) sig2_aux:
    "d2.sig p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set type_preds \<union> set (detype_preds (predicates D))"
    using t_preds_dis detype_dom_def pred_resolve d2.sig_def
    by (metis ast_domain.sel(2) set_union_code)

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

(*
  text \<open>Decompose the signature function of the detyped domain in two ways, since the domains
    are disjoint. Yes this is the best way I could think of.\<close>
  lemma (in ast_domain2) t_sig_split_a:
    "d2.sig =
      map_of (map split_pred (detype_preds (predicates D))) ++ map_of (map split_pred type_preds)"
  proof -
    let ?pred_map2 = "(map split_pred (predicates D2))"
    let ?t_pred_map = "map split_pred type_preds"
    let ?dt_pred_map = "map split_pred (detype_preds (predicates D))"

    (* d2.sig in terms of map1 ++ map2 *)
    have "d2.sig = map_of (map split_pred (type_preds @ (detype_preds (predicates D))))"
      using detype_dom_def d2.sig_def by simp
    also have "... = map_of (?t_pred_map @ ?dt_pred_map)"
      by simp
    also have "... = map_of ?dt_pred_map ++ map_of ?t_pred_map" by simp
    ultimately show ?thesis by simp
  qed

  (* d2.sig maps interchangable *)
  lemma (in wf_ast_domain2) t_sig_split_b:
    "d2.sig =
      map_of (map split_pred type_preds) ++ map_of (map split_pred (detype_preds (predicates D)))"
  proof -
    have dis: "distinct (map pred (predicates D))" using wf_D by simp

    let ?pred_map2 = "(map split_pred (predicates D2))"
    let ?t_pred_map = "map split_pred type_preds"
    let ?dt_pred_map = "map split_pred (detype_preds (predicates D))"

    have "fst \<circ> split_pred = pred"
      by (simp add: comp_def predicate_decl.case_eq_if)
    hence
      "map fst ?t_pred_map = map pred type_preds" and      
      "map fst ?dt_pred_map = map pred (predicates D)"
      using dt_preds_ids by simp_all
    hence "fst ` set ?t_pred_map \<inter> fst ` set ?dt_pred_map = {}"
      by (metis tps_dt_preds_disj dt_preds_ids list.set_map)
    hence comm: "map_of ?t_pred_map ++ map_of ?dt_pred_map = map_of ?dt_pred_map ++ map_of ?t_pred_map"
      using map_add_comm by (metis dom_map_of_conv_image_fst)
    thus ?thesis using t_sig_split_a by simp
  qed

  lemma (in wf_ast_domain2) t_sig_some:
    "d2.sig p \<noteq> None \<longleftrightarrow>
      (p \<in> pred ` set (predicates D))
      \<or> (p \<in> pred_for_type ` set type_names)"
  proof -
    have dis: "distinct (map pred (predicates D))" using wf_D by simp

    let ?pred_map2 = "(map split_pred (predicates D2))"
    let ?t_pred_map = "map split_pred type_preds"
    let ?dt_pred_map = "map split_pred (detype_preds (predicates D))"

    note t_sig_split_a
    hence "d2.sig = map_of ?dt_pred_map ++ map_of ?t_pred_map" by simp
    hence 1: "d2.sig p \<noteq> None \<longleftrightarrow>
      (p \<in> fst ` set ?dt_pred_map) \<or> (p \<in> fst ` set ?t_pred_map)"
      by (metis map_add_None map_of_eq_None_iff)

    have "fst \<circ> split_pred = pred"
      by (simp add: comp_def predicate_decl.case_eq_if)
    hence
      a: "map fst ?t_pred_map = map pred_for_type type_names" and      
      b: "map fst ?dt_pred_map = map pred (predicates D)"
      using type_preds_ids dt_preds_ids by simp_all
    hence
      "fst ` set ?t_pred_map = pred_for_type ` set type_names" and
      "fst ` set ?dt_pred_map = pred ` set (predicates D)"
       apply (metis image_set) by (metis b image_set)
    thus ?thesis using 1 by simp
  qed

  (* Using distinctness of predicates is a shortcut here.
     It's technically not required because the order of predicates is unchanged.*)
  lemma (in wf_ast_domain2) t_preds_arity:
    assumes "sig p = Some Ts"
    shows "d2.sig p = Some (replicate (length Ts) \<omega>)"
  proof -
    have dis: "distinct (map pred (predicates D))" using wf_D by simp
    let ?dt_pred_map = "map split_pred (detype_preds (predicates D))"

    have "PredDecl p Ts \<in> set (predicates D)" using assms sig_some by simp
    hence "PredDecl p (replicate (length Ts) \<omega>) \<in> set (detype_preds (predicates D))"
      using detype_preds_def by force
    hence "map_of ?dt_pred_map p = Some (replicate (length Ts) \<omega>)" using pred_resolve
      using dis dt_preds_ids by force
    thus ?thesis using t_sig_split_b by simp
  qed 

(* type pred sigs *)

  lemma (in wf_ast_domain2) type_pred_sig:
    assumes "t \<in> set type_names"
    shows "d2.sig (pred_for_type t) = Some [\<omega>]"

    using assms sig2_of_typepred type_preds_def
  proof -
    have "PredDecl (pred_for_type t) [\<omega>] \<in> set (predicates D2)"
      using type_preds_def assms detype_dom_def by fastforce
    thus ?thesis using detype_dom_def
      by (metis d2.sig_def pred_resolve t_preds_dis)
  qed *)

text \<open> type maps \<close>

  lemma (in ast_domain2) t_constT_Some: "constT c \<noteq> None \<longleftrightarrow> d2.constT c = Some \<omega>"
    using t_entT_Some ast_domain.constT_def detype_dom_def by fastforce

  lemma (in ast_domain2) t_constT_None: "constT c = None \<longleftrightarrow> d2.constT c = None"
    using t_entT_None ast_domain.constT_def detype_dom_def by fastforce

  (* lemma "distinct ((map fst m) @ (map fst n)) \<Longrightarrow> map_of m ++ map_of n = map_of n ++ map_of m"
    by (metis distinct_append dom_map_of_conv_image_fst list.set_map map_add_comm)

  lemma "map_of m ++ map_of n = map_of (n @ m)"
    by simp *)

  lemma (in ast_problem2) t_cnsts_objs_names: "map fst (consts D @ objects P)
    = map fst (detype_ents (consts D) @ detype_ents (objects P))"
    using t_ents_names by (metis map_append)

  lemma (in wf_ast_problem2) t_objm_le_objT:
    "map_of (objects P2) \<subseteq>\<^sub>m p2.objT"
  proof -
    have "distinct (map fst (consts D @ objects P))" using wf_P(1) by auto
    hence "distinct (map fst (consts D2 @ objects P2))" using t_cnsts_objs_names
      detype_dom_def detype_prob_def by (metis ast_domain.sel(3) ast_problem.sel(2))
    hence "fst ` set (objects P2) \<inter> fst ` set (consts D2) = {}"
      by auto
    hence "dom (map_of (objects P2)) \<inter> dom d2.constT = {}" using d2.constT_def
      by (simp add: dom_map_of_conv_image_fst)
    thus ?thesis using map_add_comm p2.objT_def
      by (metis ast_problem.sel(1) detype_prob_def map_le_iff_map_add_commute)
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
    by (metis ast_problem.sel(1-2) detype_prob_def map_add_None t_constT_None)

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

    lemma conj_fmlas_wf:
    assumes "\<forall>\<phi> \<in> set \<phi>s. wf_fmla tyt \<phi>"
    shows "wf_fmla tyt (conj_fmlas \<phi>s)"
    using assms apply (induction \<phi>s)
    apply simp_all
    by (metis ast_domain.wf_fmla.simps(3) conj_fmlas.simps(2-3) neq_Nil_conv)

  lemma disj_fmlas_wf:
    assumes "\<forall>\<phi> \<in> set \<phi>s. wf_fmla tyt \<phi>"
    shows "wf_fmla tyt (disj_fmlas \<phi>s)"
    using assms apply (induction \<phi>s)
    apply simp_all
    by (metis ast_domain.wf_fmla.simps(4) disj_fmlas.simps(2-3) neq_NilE)

text \<open> detype ac \<close>

  abbreviation "ac_name \<equiv> ast_action_schema.name"
  (* abbreviation (in ast_domain) "ac_params \<equiv> ast_action_schema.parameters" \<comment> just use \<open>parameters\<close> *)
  abbreviation "ac_pre \<equiv> ast_action_schema.precondition"
  abbreviation "ac_eff \<equiv> ast_action_schema.effect"

  (* TODO just manipulate lemma *)
  lemma detype_ac_alt:
    "detype_ac ac = Action_Schema
      (ac_name ac)
      (detype_ents (parameters ac))
      (param_precond (parameters ac) \<^bold>\<and> (ac_pre ac))
      (ac_eff ac)"
    apply (cases ac) by simp

  (* TODO just manipulate lemma *)
  lemma wf_ac_alt:
    "wf_action_schema a \<longleftrightarrow> (
      let
        tyt = ty_term (map_of (parameters a)) constT
      in
        distinct (map fst (parameters a))
      \<and> wf_fmla tyt (ac_pre a)
      \<and> wf_effect tyt (ac_eff a))"
    apply (cases a) by simp

  lemma ac_params_detyped:
    "\<forall>ac \<in> set (actions D2). \<forall>(n, T) \<in> set (parameters ac). T = \<omega>"
    using detype_dom_def detype_ac_alt ents_detyped by fastforce

  lemma t_ac_name: "ac_name (detype_ac ac) = ac_name ac"
    by (simp add: detype_ac_alt)
  lemma t_acs_names: "map ac_name (map detype_ac acs) = map ac_name acs"
    by (simp add: t_ac_name)
  lemma (in wf_ast_domain) t_acs_dis:
    "distinct (map ac_name (map detype_ac (actions D)))"
    using t_acs_names wf_D by metis

  lemma (in ast_domain2) t_ac_tyt:
    assumes "ty_term (map_of (parameters a)) constT x \<noteq> None"
    shows "ty_term (map_of (parameters (detype_ac a))) d2.constT x = Some \<omega>"
    using assms detype_ac_alt detype_dom_def t_tyt_Some ast_domain.constT_def by auto

  lemma params_ts_wf:
    assumes "wf_action_params a" "(n, T) \<in> set (parameters a)"
    shows "wf_type T"
    using assms wf_action_params_def by auto

  lemma params_ts_exist: (* somehow this isn't trivial for the solver *)
    assumes "wf_action_params a" "(n, Either ts) \<in> set (parameters a)"
    shows "set ts \<subseteq> set type_names"
    using assms params_ts_wf wf_type_iff_listed by blast

  lemma (in wf_ast_domain2) type_cond_wf:
    assumes "t \<in> set type_names" "tyt (term.VAR n) = Some \<omega>"
    shows "d2.wf_fmla tyt (type_cond n t)"
  proof -
    from assms(1) have "d2.sig (pred_for_type t) = Some [\<omega>]" by (rule type_pred_sig)
    hence "d2.wf_fmla tyt (Atom (predAtm (pred_for_type t) [term.VAR n]))"
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
    assumes "wf_action_params a" "p \<in> set (parameters a)"
    shows "d2.wf_fmla
      (ty_term (map_of (parameters (detype_ac a))) cnstT)
      (type_precond p)"
  proof -
    (* type_precond.cases? *)
    obtain n ts where p: "p = (n, Either ts)" using type_precond.cases by blast
    let ?tyt = "ty_term (map_of (parameters a)) cnstT"
    let ?tyt2 = "ty_term (map_of (parameters (detype_ac a))) cnstT"
    
    (* Not generally "Some (Either ts)", unless we assume wf_action_schema,
       because param names may not be distinct. *) 
    have "?tyt (term.VAR n) \<noteq> None" using assms detype_ac_alt
      by (simp add: p weak_map_of_SomeI)
    hence "?tyt2 (term.VAR n) = Some \<omega>" using t_tyt_var_Some
      by (simp add: detype_ac_alt)
    hence "\<forall>t \<in> set ts. d2.wf_fmla ?tyt2 (type_cond n t)"
      using assms p type_cond_wf params_ts_exist by blast
    hence "\<forall>\<phi> \<in> set (map (type_cond n) ts). d2.wf_fmla ?tyt2 \<phi>"
      by simp
    hence "d2.wf_fmla ?tyt2 (type_precond (n, Either ts))"
      using d2.disj_fmlas_wf type_precond.simps by metis
    thus ?thesis using p by simp
  qed

  lemma (in wf_ast_domain2) t_param_precond_wf:
    assumes "wf_action_params a"
    shows "d2.wf_fmla
    (ty_term (map_of (parameters (detype_ac a))) cnstT)
    (param_precond (parameters a))"
  proof -
    let ?tyt2 = "ty_term (map_of (parameters (detype_ac a))) cnstT"
    have "\<forall>p \<in> set (parameters a). d2.wf_fmla ?tyt2 (type_precond p)"
      using type_precond_wf assms by simp
    hence "\<forall>\<phi> \<in> set (map type_precond (parameters a)). d2.wf_fmla ?tyt2 \<phi>" by simp
    thus ?thesis using d2.conj_fmlas_wf param_precond.simps by metis
  qed

  text \<open>Three conditions: 1. distinct parameter names, 2. wf precondition, 3. wf effect\<close>
  lemma (in restr_domain2) t_ac_wf:
    assumes "a \<in> set (actions D)"
    shows "d2.wf_action_schema (detype_ac a)"
  proof -
    let ?a2 = "detype_ac a"
    let ?tyt = "ty_term (map_of (parameters a)) constT"
    let ?tyt2 = "ty_term (map_of (parameters (detype_ac a))) d2.constT"

    have tyt_om: "\<forall>x. ?tyt x \<noteq> None \<longrightarrow> ?tyt2 x = Some \<omega>" using t_ac_tyt by simp
    from assms have wfa: "wf_action_schema a" using wf_D(7) by simp

    from assms have "distinct (map fst (parameters a))" using wfa wf_ac_alt by metis
    hence c1: "distinct (map fst (parameters ?a2))" using t_ents_dis detype_ac_alt by auto

    from assms have "wf_fmla ?tyt (ac_pre a)" using wfa wf_ac_alt by metis
    hence c2b: "d2.wf_fmla ?tyt2 (ac_pre a)" using tyt_om t_fmla_wf by blast
    have "wf_action_params a" using restr_D(2) assms by simp
    note c2a = t_param_precond_wf[OF this]
    from c2a c2b have c2: "d2.wf_fmla ?tyt2 (ac_pre ?a2)" by (simp add: detype_ac_alt)

    from assms have "wf_effect ?tyt (ac_eff a)" using wfa wf_ac_alt by metis
    hence "d2.wf_effect ?tyt2 (ac_eff a)"
      using tyt_om ast_domain.wf_effect.simps t_eff_wf detype_ac_alt by blast
    hence c3: "d2.wf_effect ?tyt2 (ac_eff ?a2)" using detype_ac_alt by simp

    from c1 c2 c3 show ?thesis using d2.wf_ac_alt by simp
  qed

  lemma (in restr_domain2) t_acs_wf:
    shows "(\<forall>a\<in>set (map detype_ac (actions D)). d2.wf_action_schema a)"
    using detype_dom_def wf_D t_ac_wf by simp

(* --------------------------------------------------------------------- *)

text \<open> init / goal \<close> (* TODO maybe move elsewhere *)

  abbreviation (input) get_t :: "type \<Rightarrow> name" where
    "get_t T \<equiv> hd (primitives T)"
  lemma "get_t (Either ts) = hd ts" by simp

  lemma "distinct (supertypes_of t)" using reachable_dis by metis

  lemma superfacts_for_cond:
    assumes "single_type T"
    shows "supertype_facts_for (n, T) =
        map (Atom \<circ> (\<lambda>p. predAtm p [n])) (supertype_preds (get_t T))"
    using assms type.collapse supertype_facts_for.simps(1)
    using list.sel(1) list_decomp_1 sorry

  lemma a: "distinct (supertype_preds t)"
    using supertype_preds_def reachable_dis pred_for_type_dis by metis

  lemma b:
    assumes "distinct preds"
    shows "distinct (map (\<lambda>p. predAtm p args) preds)"
  proof -
    have "inj (\<lambda>p. predAtm p args)" 
      by (simp add: inj_def)
    thus ?thesis
      using assms map_inj_dis by fastforce
  qed

  

  lemma c: "distinct (supertype_facts_for (n, Either [t]))"
  proof -
    have dis: "distinct (map (\<lambda>p. predAtm p [n]) (supertype_preds t))"
      using a b by auto
    have inj: "inj Atom" by (simp add: inj_def)
    note map_inj_dis[OF dis inj]
    thus ?thesis by simp
  qed

  lemma c': "single_type T \<Longrightarrow> distinct (supertype_facts_for (n, T))"
    using c
    by (metis list_decomp_1 type.collapse)


  lemma d:
    assumes "n \<noteq> m"
    shows "set (supertype_facts_for (n, Either [t1])) \<inter> set (supertype_facts_for (m, Either [t2])) = {}"
    (is "?l \<inter> ?r = {}")
  proof -
    have "x \<noteq> y" if "x \<in> ?l \<and> y \<in> ?r" for x y
    proof -
      from that obtain k where 1: "x = Atom k" "atom.arguments k = [n]" by auto
      from that obtain g where 2: "y = Atom g" "atom.arguments g = [m]" by auto
      from 1 2 show ?thesis using assms by fastforce
    qed
    thus ?thesis by auto
  qed

  lemma d': assumes "n \<noteq> m" "single_type T1" "single_type T2"
    shows "set (supertype_facts_for (n, T1)) \<inter> set (supertype_facts_for (m, T2)) = {}"
    using assms d
    by (metis list_decomp_1 type.collapse)
  
  lemma d'': assumes "n \<notin> fst ` set cs" "single_types cs" "single_type T"
    shows "set (supertype_facts_for (n, T)) \<inter> set (supertype_facts cs) = {}"
    (is "?l \<inter> ?r = {}")
    using d' sorry

  lemma "\<lbrakk>length (primitives T) = 1; \<And>t. P (Either [t]) t\<rbrakk> \<Longrightarrow> P T (hd (primitives T))"
    by (metis list.sel(1) list_decomp_1 type.collapse)

  lemma h:
    assumes
      "x \<in> set (supertype_facts_for (n, Either [t]))"
    shows "\<exists> st. st \<in> set (supertypes_of t) \<and>
                 x = Atom (predAtm (pred_for_type st) [n])"
  proof -
    from assms obtain st where
      stin: "st \<in> set (supertypes_of t)" and
      x: "x = Atom (predAtm (pred_for_type st) [n])"
      by (auto simp add: supertype_preds_def)
    thus ?thesis by simp
  qed

  lemma h':
    assumes
      "x \<in> set (supertype_facts_for (n, T))" "single_type T"
    shows "\<exists> st. st \<in> set (supertypes_of (hd (primitives T))) \<and>
                 x = Atom (predAtm (pred_for_type st) [n])"
    using assms
    by (simp add: h superfacts_for_cond)

  lemma q: "pred ` set (predicates D) \<inter> pred ` (set type_preds) = {}"
    by (metis Int_commute dt_preds_ids image_set tps_dt_preds_disj)

  lemma (in wf_ast_problem) r: assumes "x \<in> set (init P)"
    shows "\<exists>p \<in> pred ` set (predicates D). \<exists>args. x = Atom (predAtm p args)"
  proof -
    from assms have 1: "wf_fmla_atom objT x"
      by (meson wf_world_model_def wf_P)
    then obtain a vs where 2: "x = Atom (predAtm a vs)"
      using wf_fmla_atom.elims(2) by blast
    from 1 2 have "wf_pred_atom objT (a, vs)" by simp
    hence "sig a \<noteq> None"
      by (metis option.simps(4) wf_pred_atom.simps)
    hence "a \<in> pred ` set (predicates D)"
      by (metis image_eqI option.exhaust predicate_decl.sel(1) sig_some)
    from this 2 show ?thesis by simp
  qed

  lemma i:
  assumes "single_types ents"
  shows "\<forall>x \<in> set (supertype_facts ents). \<exists> t a. x = Atom (predAtm (pred_for_type t) a)"
  using assms h' supertype_facts_def by fastforce

  lemma e:
  assumes "distinct (map fst objs)" "single_types objs"
  shows "distinct (supertype_facts objs)"
  using assms proof (induction objs)
    case (Cons ob obs)
    hence notin: "fst ob \<notin> fst ` set obs" by auto
    hence int: "set (supertype_facts_for ob) \<inter> set (supertype_facts obs) = {}"
      using d''[OF notin] Cons.prems by fastforce
    from Cons have dis2: "distinct (supertype_facts obs)" by simp
    from c' Cons.prems have "distinct (supertype_facts_for ob)" by auto
    thus ?case using int dis2 supertype_facts_def by simp
  qed (simp add: supertype_facts_def)

  (* doesn't really matter because if I can't prove it, I'll just throw remdups at it *)
  lemma (in restr_problem) t_init_dis: "distinct (init P2)"
  proof -
    have 0: "init P2 = supertype_facts (objects P) @ supertype_facts (consts D) @ (init P)"
      using detype_prob_def by simp
    have 1: "distinct (map fst ((consts D) @ (objects P)))" using wf_P by fastforce
    have 2: "single_types (consts D @ objects P)"
      using single_t_objs by auto
    from 1 2 have "distinct (supertype_facts (consts D @ objects P))" using e by simp
    hence dis1: "distinct (supertype_facts (objects P) @ supertype_facts (consts D))"
      using supertype_facts_def by auto
    have dis2: "distinct (init P)" using wf_P by auto
    have int: "set (supertype_facts (consts D @ objects P)) \<inter> set (init P) = {}" sorry

    from dis1 dis2 int 0 supertype_facts_def show ?thesis by auto
  qed

  lemma (in wf_ast_domain) supertypes_listed:
    assumes "t \<in> set type_names"
    shows "set (supertypes_of t) \<subseteq> set type_names"
  proof -
    (* why is this so tedious? *)
    have 1: "snd ` set (types D) \<subseteq> set type_names"
      using wf_D wf_types_def type_names_set by simp
  
    have "set (supertypes_of t) \<subseteq> insert t (snd ` set (types D))"
      using reachable_set by simp
    also have "... \<subseteq> insert t (set type_names)" using 1 by blast
    also have "... \<subseteq> set type_names" using assms by simp
  
    ultimately show ?thesis by blast
  qed

  thm wf_ast_domain2.type_pred_sig

  (* TODO simplify *)
  lemma (in wf_ast_problem2) super_facts_for_wf:
    assumes "length (primitives T) = 1"
      "(n, T) \<in> set (consts D @ objects P)"
    shows "\<forall>\<phi> \<in> set (supertype_facts_for (n, T)). d2.wf_fmla_atom p2.objT \<phi>"
  proof
    fix \<phi> assume phi_in: "\<phi> \<in> set (supertype_facts_for (n, T))"

    from assms obtain t where t: "T = Either [t]"
      by (metis list_decomp_1 type.collapse)
    hence "supertype_facts_for (n, T) = map (Atom \<circ> (\<lambda>p. predAtm p [n])) (supertype_preds t)"
      by simp
    from this phi_in obtain sp where
      sp_in: "sp \<in> set (supertype_preds t)" and
      phi: "\<phi> = Atom (predAtm sp [n])" by auto
    from this obtain st where
      sp: "sp = pred_for_type st" and
      st_in: "st \<in> set (supertypes_of t)" using supertype_preds_def by auto

    from assms(2) have "wf_type T" using wf_DP by auto
    hence tin: "t \<in> set type_names" using wf_type_iff_listed t by simp
    from this st_in have st_in': "st \<in> set type_names" using supertypes_listed by blast
    from tin have "\<forall>st \<in> set (supertypes_of t). st \<in> set type_names"
      using supertypes_listed by blast

    note type_pred_sig[OF st_in']
    hence sp_sig: "d2.sig sp = Some [\<omega>]" using sp by simp

    from assms(2) have "objT n \<noteq> None" using objT_Some by simp
    hence n_obj: "p2.objT n = Some \<omega>" using t_objT_Some by simp

    from phi show "d2.wf_fmla_atom p2.objT \<phi>"
      using sp_sig n_obj d2.is_of_type_def by fastforce
  qed

  lemma (in wf_ast_problem2) super_facts_wf:
    assumes "single_types ents"
      "set ents \<subseteq> set (consts D @ objects P)"
    shows "\<forall>\<phi> \<in> set (supertype_facts ents). d2.wf_fmla_atom p2.objT \<phi>"
    using assms supertype_facts_def super_facts_for_wf by fastforce

  lemma (in restr_problem2) t_init_wf:
    "p2.wf_world_model (set (init P2))"
  proof -
    have 1: "\<forall>c. (objT c \<noteq> None) \<longrightarrow> (p2.objT c = Some \<omega>)" using t_objT_Some by simp
    have "\<forall>\<phi> \<in> set (init P). wf_fmla_atom objT \<phi>"
      using wf_world_model_def wf_P by simp
    hence c1: "\<forall>\<phi> \<in> set (init P). p2.wf_fmla_atom p2.objT \<phi>"
      using t_fmla_atom_wf 1 by (auto simp add: detype_prob_def)

    have c23: "\<forall>\<phi> \<in> set (supertype_facts (consts D @ objects P)). d2.wf_fmla_atom p2.objT \<phi>"
      using super_facts_wf single_t_objs by blast
    
    from c1 c23 show ?thesis
      using detype_prob_def supertype_facts_def p2.wf_world_model_def by auto
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
    have "distinct (map fst (consts D))" using wf_D by simp
    hence c4: "distinct (map fst (detype_ents(consts D)))"
      by (simp add: t_ents_dis)
    have c5: "(\<forall>(n,T)\<in>set (detype_ents (consts D)). d2.wf_type T)"
      using t_ents_wf by metis
    have c6: "distinct (map ac_name (map detype_ac (actions D)))"
      using t_acs_dis by simp
    note c7 = t_acs_wf
  
    from c1 c2 c3 c4 c5 c6 c7 show ?thesis
      using d2.wf_domain_def detype_dom_def by auto
  qed

  theorem (in restr_problem2) detype_prob_wf:
    shows "p2.wf_problem"
  proof -
    note c1 = detype_dom_wf
    have "distinct (map fst (objects P) @ map fst (consts D))" using wf_P by simp
    hence c2: "distinct (map fst (detype_ents (objects P)) @ map fst (detype_ents (consts D)))"
      using t_ents_names by metis
    have c3: "\<forall>(n, y)\<in>set (objects P2). p2.wf_type y"
      using t_ents_wf detype_prob_def by fastforce
    note c4 = t_init_dis
    note c5 = t_init_wf
  
    have c6a: "\<forall>e. objT e \<noteq> None \<longrightarrow> p2.objT e = Some \<omega>" using t_objT_Some by simp
    have c6b: "wf_fmla objT (goal P2)" using detype_prob_def wf_P by simp
    have c6: "p2.wf_fmla p2.objT (goal P2)"
      using t_fmla_wf[OF c6a c6b] detype_prob_def by simp
    from c1 c2 c3 c4 c5 c6 show ?thesis
      using p2.wf_problem_def detype_prob_def detype_dom_def by simp
  qed

end

subsubsection \<open> Type Normalization Preserves Semantics \<close>

context ast_domain
begin

text \<open> Supertype Enumeration \<close>

  lemma of_type_iff_reach:
    shows "of_type oT T \<longleftrightarrow> (
      \<forall>ot \<in> set (primitives oT).
      \<exists>t \<in> set (primitives T).
        t \<in> set (supertypes_of ot))"
  proof -
    have "subtype_rel = set (map prod.swap (types D))"
      using subtype_rel_def subtype_edge_swap by metis
    hence subrel_inv: "subtype_rel = (set (types D))\<inverse>" by auto
    hence "of_type oT T \<longleftrightarrow>
      set (primitives oT) \<subseteq> ((set (types D))\<inverse>)\<^sup>* `` set (primitives T)"
      using of_type_def by simp
    also have "... \<longleftrightarrow>
      set (primitives oT) \<subseteq> ((set (types D))\<^sup>*)\<inverse> `` set (primitives T)"
      by (simp add: rtrancl_converse)
    also have "... \<longleftrightarrow>
      (\<forall>ot \<in> set (primitives oT). ot \<in> ((set (types D))\<^sup>*)\<inverse> `` set (primitives T))"
      by auto
    also have "... \<longleftrightarrow>
      (\<forall>ot \<in> set (primitives oT). \<exists>t. (ot, t) \<in> (set (types D))\<^sup>* \<and> t \<in> set (primitives T))"
      by auto
    finally show ?thesis using reachable_iff_in_star by metis
  qed

  lemma (in ast_problem) obj_of_type_iff_reach:
    assumes "objT n = Some oT"
    shows  "is_obj_of_type n T \<longleftrightarrow>
      (\<forall>ot \<in> set (primitives oT).
        \<exists>t \<in> set (primitives T).
      t \<in> set (supertypes_of ot))"
    using assms is_obj_of_type_def of_type_iff_reach by auto

  lemma (in ast_domain) single_of_type_iff:
    shows "of_type (Either [ot]) T \<longleftrightarrow> (
      \<exists>t \<in> set (primitives T).
        t \<in> set (supertypes_of ot))"
    using of_type_iff_reach by simp

  lemma (in ast_problem) simple_obj_of_type_iff:
    assumes "objT n = Some (Either [ot])"
    shows  "is_obj_of_type n T \<longleftrightarrow>
        (\<exists>t \<in> set (primitives T).
      t \<in> set (supertypes_of ot))"
    using assms is_obj_of_type_def single_of_type_iff by auto



end

text \<open> major \<close>

context restr_problem2
begin

abbreviation "super_facts \<equiv> supertype_facts (objects P @ consts D)"
abbreviation "sf_substate \<equiv> set super_facts"

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


(* ---------------------- Future Milestones ------------------------- *)

(* type normalization correct w.r.t. execution*)




end