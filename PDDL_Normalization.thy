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
abbreviation singleton_types :: "('a \<times> type) list \<Rightarrow> bool" where
  "singleton_types os \<equiv> (\<forall>(_, t) \<in> set os. length (primitives t) = 1)"

context ast_domain
begin
  (* Omitting this from wf_action_schema is a little annoying for me *)
  definition wf_action_params :: "ast_action_schema \<Rightarrow> bool" where
    "wf_action_params a \<equiv> (\<forall>t \<in> snd ` (set (parameters a)). wf_type t)"
  
  definition restrict_dom :: bool where
    "restrict_dom \<equiv> singleton_types (consts D)
                    \<and> (\<forall>a\<in>set (actions D). wf_action_params a)"
end

locale restr_domain = wf_ast_domain +
  assumes restrD: restrict_dom
begin
  (* this is the most important and most referenced property restriction *)
  lemma single_t_cnsts: "singleton_types (consts D)"
    using restrD by (auto simp add: restrict_dom_def)
end

context ast_problem
begin
  definition restrict_prob :: bool where
    "restrict_prob \<equiv> restrict_dom
                  \<and> singleton_types (objects P)
                  \<and> only_conj (goal P)"
end

locale restr_problem = wf_ast_problem +
  assumes restrP: restrict_prob
begin
  sublocale restr_domain "domain P"
    apply unfold_locales
    using restrP
    unfolding restrict_prob_def by simp

  lemma single_t_cnsts: "singleton_types (objects P)"
    using restrP by (auto simp add: restrict_dom_def restrict_prob_def)
end

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
  
  text \<open>This only works for singleton types on purpose.\<close>
  fun supertype_facts_for :: "(object \<times> type) \<Rightarrow> object atom formula list" where
    "supertype_facts_for (n, Either [t]) =
      map (Atom \<circ> (\<lambda>p. predAtm p [n])) (supertype_preds t)" |
    "supertype_facts_for (n, _) = undefined"

  (* TODO sugar *)
  fun type_conds :: "type \<Rightarrow> predicate list" where
    "type_conds t = map pred_for_type (primitives t)"
  
  fun type_precond :: "(variable \<times> type) \<Rightarrow> term atom formula" where
    "type_precond (v, T) =
      disj_fmlas (map (Atom \<circ> (\<lambda>p. predAtm p [term.VAR v])) (type_conds T))"
  
  fun param_precond :: "(variable \<times> type) list \<Rightarrow> term atom formula" where
    "param_precond params = conj_fmlas (map type_precond params)"

  abbreviation detype_pred :: "predicate_decl \<Rightarrow> predicate_decl" where
    "detype_pred p \<equiv> PredDecl (pred p) (replicate (length (argTs p)) \<omega>)"

  definition detype_preds :: "predicate_decl list \<Rightarrow> predicate_decl list" where
    "detype_preds preds \<equiv> map detype_pred preds"

  abbreviation detype_ent :: "('ent \<times> type) \<Rightarrow> ('ent \<times> type)" where
    "detype_ent ent \<equiv> (fst ent, \<omega>)"

  definition detype_ents :: "('ent \<times> type) list \<Rightarrow> ('ent \<times> type) list" where
    "detype_ents params \<equiv> map detype_ent params"

  fun detype_ac :: "ast_action_schema \<Rightarrow> ast_action_schema" where
  "detype_ac (Action_Schema nam params pre eff) =
    Action_Schema nam (detype_ents params) (param_precond params \<^bold>\<and> pre) eff"
  (* TODO other alternative *)
  lemma detype_ac_def:
    "detype_ac ac = Action_Schema
      (ast_action_schema.name ac)
      (detype_ents (ast_action_schema.parameters ac))
      (param_precond (ast_action_schema.parameters ac) \<^bold>\<and> (ast_action_schema.precondition ac))
      (ast_action_schema.effect ac)"
    by (metis ast_action_schema.collapse detype_ac.simps)

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

text \<open>This is mostly to simplify the syntax, actually. So I can just do
   \<open>Dt.some_function\<close> instead of \<open>ast_domain.some_function detype_dom\<close>.
    But I'm not using it (yet) as the cleaner syntax doesn't offset the added confusion.\<close>
(*locale ast_domain2 = ast_domain
sublocale ast_domain2 \<subseteq> Dt: ast_domain detype_dom .
locale wf_ast_domain2 = wf_ast_domain
sublocale wf_ast_domain2 \<subseteq> Dt: ast_domain detype_dom .
locale ast_problem2 = ast_problem
sublocale ast_problem2 \<subseteq> Pt: ast_problem detype_prob . *)

subsection \<open>Type Normalization Proofs\<close>

subsubsection \<open> Type Normalization Produces Typeless PDDL \<close>

context ast_domain
begin

  lemma preds_detyped: "\<forall>p \<in> set (predicates detype_dom). \<forall>T \<in> set (argTs p). T = \<omega>"
    using type_preds_def detype_preds_def detype_dom_def by auto
  
  lemma ents_detyped: "\<forall>(n, T) \<in> set (detype_ents ents). T = \<omega>"
    unfolding detype_ents_def
    by (simp add: case_prod_beta' detype_dom_def)
  
  lemma ac_params_detyped:
    "\<forall>ac \<in> set (actions detype_dom). \<forall>(n, T) \<in> set (parameters ac). T = \<omega>"
    using detype_dom_def detype_ac_def ents_detyped by fastforce
  
  lemma dom_detyped:
    "ast_domain.typeless_dom detype_dom"
  proof -
    have c1: "types detype_dom = []" using detype_dom_def by simp
    note c2 = preds_detyped
    have c3: "\<forall>(n, T) \<in> set (consts detype_dom). T = \<omega>"
      by (simp add: detype_dom_def ents_detyped)
    note c4 = ac_params_detyped
  
    from c1 c2 c3 c4 show ?thesis
      using ast_domain.typeless_dom_def by simp
  qed
end

lemma (in ast_problem) prob_detyped:
  "ast_problem.typeless_prob detype_prob"
proof -
  have "\<forall>(n, T) \<in> set (objects detype_prob). T = \<omega>"
    by (simp add: detype_prob_def ents_detyped)
  thus ?thesis using dom_detyped ast_problem.typeless_prob_def detype_prob_def by simp
qed

subsubsection \<open> Type Normalization Preserves Well-Formedness \<close>

(* Properties of type system *)

context ast_domain
begin
  
  lemma subtype_edge_swap: "subtype_edge = prod.swap"
  proof -
    have "\<And>a b. subtype_edge (a, b) = prod.swap (a, b)"
      by simp
    thus ?thesis by fast
  qed
  
  lemma wf_object: "ast_domain.wf_type d \<omega>"
    unfolding ast_domain.wf_type.simps by simp

  lemma tyterm_prop: "P (ty_term varT cnstT x) \<longleftrightarrow>
    (case x of term.VAR x' \<Rightarrow> P (varT x') |
               term.CONST x' \<Rightarrow> P (cnstT x'))"
    apply (split term.split)
    by simp
  
  lemma tyterm_elem: "(ty_term (map_of varT) (map_of cnstT) x \<noteq> None)
    \<longleftrightarrow> (case x of term.VAR x' \<Rightarrow> x' \<in> fst ` set varT |
                   term.CONST x' \<Rightarrow> x' \<in> fst ` set cnstT)"
    apply (split term.split)
    using tyterm_prop by (simp add: map_of_eq_None_iff)

  (* supertype enumeration *)
  
  lemma wf_type_iff_listed: "wf_type (Either ts) \<longleftrightarrow> (\<forall>t \<in> set ts. t \<in> set (type_names))"
  proof -
    have "set type_names = insert ''object'' (fst ` set (types D))"  by auto
    thus ?thesis by (simp add: subset_code(1))
  qed

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

  lemma type_preds_ids: "map pred type_preds = map pred_for_type type_names"
    using type_preds_def by simp

  lemma p_is_tp: "p \<in> pred ` set type_preds \<longleftrightarrow> (\<exists>t \<in> set type_names. p = pred_for_type t)"
  (* by force takes 9 seconds *)
  proof -
    have "pred ` set type_preds = pred_for_type ` set type_names"
      by (metis type_preds_ids list.set_map)
    thus ?thesis by auto
  qed
end


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

(* well-formedness *)

lemma dist_pred: "distinct names \<longleftrightarrow> distinct (map Pred names)"
  by (meson distinct_map inj_onI predicate.inject)

context wf_ast_domain
begin
  lemmas wf_dom_def = wf_domain[unfolded wf_domain_def]

  lemma (in ast_domain) dt_pred_name: "pred (detype_pred pd) = pred pd" by simp
  lemma (in ast_domain) dt_preds_names:
    "map pred (detype_preds ps) = map pred ps"
    using dt_pred_name detype_preds_def by simp
  lemma (in ast_domain) tps_dis:
    "distinct (map pred type_preds)" (is "distinct ?tp_ids")
  proof -
    let ?pred_ids = "map pred (predicates D)"
    let ?prefix = "safe_prefix (map predicate.name ?pred_ids)"
    have tp_ids: "?tp_ids = map (Pred \<circ> ((@) ?prefix)) type_names"
        by (simp add: type_preds_def)
    have "distinct (map ((@) ?prefix) type_names)" (* because: distinct type_names *)
      using dist_prefix by simp
    hence "distinct (map (Pred \<circ> ((@) ?prefix)) type_names)"
      using dist_pred by simp
    thus "distinct ?tp_ids" using tp_ids by metis
  qed

  (* TODO simplify *)
  lemma (in ast_domain) tps_dt_preds_disj:
    "pred ` set type_preds \<inter> pred ` set (detype_preds (predicates D)) = {}"
  proof -
    let ?preds = "map pred (predicates D)"
    let ?t_preds = "map pred type_preds"
    let ?dt_preds = "map pred (detype_preds (predicates D))"

    let ?prefix = "safe_prefix (map predicate.name ?preds)"
    (* =  map (pred_for_type D) (type_names D) *)
    have t_ps_expand: "?t_preds = map (Pred \<circ> ((@) ?prefix)) type_names"
      by (simp add: type_preds_def)
    (* define, not let, because the terms become too big for the solver *)
    define pnames where "pnames \<equiv> map predicate.name ?preds"
    define tp_names where "tp_names \<equiv> map (((@) (safe_prefix pnames))) type_names"
    
    have "set (map ((@) (safe_prefix pnames)) type_names) \<inter> set pnames = {}"
      using safe_prefix_correct by auto
    hence "set tp_names \<inter> set pnames = {}" using tp_names_def pnames_def by simp
    hence "set (map Pred tp_names) \<inter> set (map Pred pnames) = {}" by auto
    hence "set (map (Pred \<circ> ((@) (safe_prefix pnames))) type_names) \<inter> set (map Pred pnames) = {}"
      using tp_names_def by (metis map_map)
  
    moreover have "map Pred pnames = ?preds" using pnames_def by simp
    moreover have "?t_preds = map (Pred \<circ> ((@) (safe_prefix pnames))) type_names"
      using t_ps_expand pnames_def by blast
    ultimately have g2: "set ?t_preds \<inter> set ?dt_preds = {}" by (metis dt_preds_names)
    thus ?thesis by simp
  qed

  lemma t_preds_dis:
    shows "distinct (map pred (predicates detype_dom))"
  proof -
    (* Predicate names are unique because the original predicate names are unchanged
       and the additional predicate names are unique (based on unique type names)
       and distinct from the original predicates. *)

    have c1: "distinct (map pred (detype_preds (predicates D)))"
      using dt_preds_names wf_dom_def by simp
    note c2 = tps_dt_preds_disj
    note c3 = tps_dis
  
    from c1 c2 c3 have "distinct (map pred (type_preds @ detype_preds (predicates D)))" by simp
    thus ?thesis using ast_domain.sel(2) detype_dom_def by presburger
  qed

  lemma (in ast_domain) t_preds_wf:
      "\<forall>p \<in> set (predicates detype_dom). ast_domain.wf_predicate_decl detype_dom p"
    proof -
      have "\<forall>p \<in> set (predicates detype_dom). \<forall>T \<in> set (argTs p). T = \<omega>"
        by (rule preds_detyped)
      hence "\<forall>p \<in> set (predicates detype_dom). \<forall>T \<in> set (argTs p). ast_domain.wf_type detype_dom T"
        using preds_detyped wf_object by auto
      thus ?thesis by (metis ast_domain.wf_predicate_decl.simps predicate_decl.collapse)
    qed
  
  lemma (in ast_domain) t_ents_names:
    "map fst (detype_ents ents) = map fst ents"
    unfolding detype_ents_def by auto

  lemma (in ast_domain) t_ents_dis:
    assumes "distinct (map fst ents)"
    shows "distinct (map fst (detype_ents ents))"
    using assms by (metis t_ents_names)

  lemma (in ast_domain) t_ents_wf:
    shows "(\<forall>(n,T)\<in>set (detype_ents ents). ast_domain.wf_type detype_dom T)"
    using ents_detyped wf_object by fast

  (* predicate signatures *)
  abbreviation "split_pred \<equiv> (\<lambda>PredDecl p n \<Rightarrow> (p, n))"

  lemma pred_resolve:
    assumes "distinct (map pred preds)"
    shows "map_of (map split_pred preds) p = Some Ts
      \<longleftrightarrow> PredDecl p Ts \<in> set preds"
  proof -
    let ?pred_map = "map split_pred preds"
    have fst_split: "fst \<circ> split_pred = pred"
      by (simp add: comp_def predicate_decl.case_eq_if)
    hence "distinct (map fst ?pred_map)" using assms by simp
    hence 1: "map_of ?pred_map p = Some Ts \<longleftrightarrow> (p, Ts) \<in> set ?pred_map" by simp

    (* this direction seems to be harder to infer automatically *)
    moreover have "\<And>pred. split_pred pred = (p, Ts) \<Longrightarrow> pred = PredDecl p Ts"
      by (metis predicate_decl.case predicate_decl.exhaust prod.inject)
    hence "(p, Ts) \<in> set ?pred_map \<longleftrightarrow> PredDecl p Ts \<in> set preds"
      by force
    thus ?thesis using 1 by presburger
  qed

  lemma sig_some:
    "sig p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set (predicates D)"
  proof -
    have "distinct (map pred (predicates D))" using wf_dom_def by simp
    thus ?thesis using pred_resolve sig_def by simp
  qed

  text \<open>Decompose the signature function of the detyped domain in two ways, since the domains
    are disjoint. Yes this is the best way I could think of.\<close>
  lemma t_sig_split_a:
    "ast_domain.sig detype_dom =
      map_of (map split_pred (detype_preds (predicates D))) ++ map_of (map split_pred type_preds)"
  proof -
    interpret d2 : ast_domain detype_dom .
    let ?pred_map2 = "(map split_pred (predicates detype_dom))"
    let ?t_pred_map = "map split_pred type_preds"
    let ?dt_pred_map = "map split_pred (detype_preds (predicates D))"

    (* d2.sig in terms of map1 ++ map2 *)
    have "d2.sig = map_of ?pred_map2"
      by (simp add: d2.sig_def)
    also have "... = map_of (map split_pred (type_preds @ (detype_preds (predicates D))))"
      using detype_dom_def by simp
    also have "... = map_of (?t_pred_map @ ?dt_pred_map)"
      by simp
    also have "... = map_of ?dt_pred_map ++ map_of ?t_pred_map" by simp
    ultimately show ?thesis by simp
  qed

  (* d2.sig maps interchangable *)
  lemma t_sig_split_b:
    "ast_domain.sig detype_dom =
      map_of (map split_pred type_preds) ++ map_of (map split_pred (detype_preds (predicates D)))"
  proof -
    interpret d2 : ast_domain detype_dom .
    have dis: "distinct (map pred (predicates D))" using wf_dom_def by simp

    let ?pred_map2 = "(map split_pred (predicates detype_dom))"
    let ?t_pred_map = "map split_pred type_preds"
    let ?dt_pred_map = "map split_pred (detype_preds (predicates D))"

    have "fst \<circ> split_pred = pred"
      by (simp add: comp_def predicate_decl.case_eq_if)
    hence
      "map fst ?t_pred_map = map pred type_preds" and      
      "map fst ?dt_pred_map = map pred (predicates D)"
      using dt_preds_names by simp_all
    hence "fst ` set ?t_pred_map \<inter> fst ` set ?dt_pred_map = {}"
      by (metis tps_dt_preds_disj dt_preds_names list.set_map)
    hence comm: "map_of ?t_pred_map ++ map_of ?dt_pred_map = map_of ?dt_pred_map ++ map_of ?t_pred_map"
      using map_add_comm by (metis dom_map_of_conv_image_fst)
    thus ?thesis using t_sig_split_a by simp
  qed

  lemma t_sig_some:
    "ast_domain.sig detype_dom p \<noteq> None \<longleftrightarrow>
      (p \<in> pred ` set (predicates D))
      \<or> (p \<in> pred_for_type ` set type_names)"
  proof -
    interpret d2 : ast_domain detype_dom .
    have dis: "distinct (map pred (predicates D))" using wf_dom_def by simp

    let ?pred_map2 = "(map split_pred (predicates detype_dom))"
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
      using type_preds_ids dt_preds_names by simp_all
    hence
      "fst ` set ?t_pred_map = pred_for_type ` set type_names" and
      "fst ` set ?dt_pred_map = pred ` set (predicates D)"
       apply (metis image_set) by (metis b image_set)
    thus ?thesis using 1 by simp
  qed

  (* Using distinctness of predicates is a shortcut here.
     It's technically not required because the order of predicates is unchanged.*)
  lemma t_preds_arity:
    assumes "sig p = Some Ts"
    shows "ast_domain.sig detype_dom p = Some (replicate (length Ts) \<omega>)"
  proof -
    have dis: "distinct (map pred (predicates D))" using wf_dom_def by simp
    let ?dt_pred_map = "map split_pred (detype_preds (predicates D))"

    have "PredDecl p Ts \<in> set (predicates D)" using assms sig_some by simp
    hence "PredDecl p (replicate (length Ts) \<omega>) \<in> set (detype_preds (predicates D))"
      using detype_preds_def by force
    hence "map_of ?dt_pred_map p = Some (replicate (length Ts) \<omega>)" using pred_resolve
      using dis dt_preds_names by force
    thus ?thesis using t_sig_split_b by simp
  qed

  lemma "map_of m x \<noteq> None \<longleftrightarrow> x \<in> fst ` set m"
    by (simp add: map_of_eq_None_iff)

  (* formulas *)
  lemma "constT x \<noteq> None \<longleftrightarrow> (x \<in> fst ` set (consts D))"
    using constT_def by (simp add: map_of_eq_None_iff)

  lemma t_entT:
    assumes "x \<in> fst ` set ents"
    shows "map_of (detype_ents ents) x = Some \<omega>"
  proof -
    have "map fst ents = map fst (detype_ents ents)" using t_ents_names by metis
    hence x: "x \<in> fst ` set (detype_ents ents)" using assms by (metis image_set)
    have "\<forall>T \<in> snd ` set (detype_ents ents). T = \<omega>"
      using detype_dom_def ents_detyped by fastforce
    thus ?thesis
      using x img_snd map_of_SomeD map_of_eq_None_iff option.exhaust by metis
  qed

  lemma t_constT: "x \<in> fst ` set (consts D) \<Longrightarrow> ast_domain.constT detype_dom x = Some \<omega>"
    using detype_dom_def ast_domain.constT_def t_entT by simp

  lemma t_tyt_some:
    assumes "ty_term (map_of vars) (map_of cnsts) e \<noteq> None"
    shows "ty_term (map_of (detype_ents vars)) (map_of (detype_ents cnsts)) e = Some \<omega>"
    using assms apply (induction e)
    apply (metis t_entT map_of_eq_None_iff ty_term.simps(1))
    apply (metis t_entT map_of_eq_None_iff ty_term.simps(2))
    done

  thm of_type_refl
  lemma t_tyt_params:
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "list_all2 (is_of_type tyt) params Ts"
    shows "list_all2 (ast_domain.is_of_type detype_dom tyt2) params (replicate (length Ts) \<omega>)"
  proof -
    interpret d2 : ast_domain detype_dom .
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

  thm wf_pred_atom.simps
  lemma
    assumes "\<forall>e. tyt e \<noteq> None \<longrightarrow> tyt2 e = Some \<omega>"
      "wf_atom tyt a"
    shows
      "ast_domain.wf_atom detype_dom tyt2 a"
  proof -
    interpret d2 : ast_domain detype_dom .
    from assms show ?thesis
    proof (induction a)
      case (predAtm p params)
      (* these follow from the definition of wf_pred_atom *)
      then obtain Ts where sigp: "sig p = Some Ts" by fastforce
      from predAtm this have 1: "list_all2 (is_of_type tyt) params Ts" by simp

      let ?os = "replicate (length Ts) \<omega>"
      from assms 1 have a: "list_all2 (d2.is_of_type tyt2) params ?os"
        by (simp add: t_tyt_params)
      have b: "d2.sig p = Some ?os" using sigp by (simp add: t_preds_arity)

      from a b show ?case by
        (simp add: ast_domain.wf_pred_atom.simps ast_domain.wf_atom.simps(1))
    qed simp
  qed

  (* actions *)
  abbreviation (in ast_domain) "ac_name \<equiv> ast_action_schema.name"
  (* abbreviation (in ast_domain) "ac_params \<equiv> ast_action_schema.parameters" \<comment> just use \<open>parameters\<close> *)
  abbreviation (in ast_domain) "ac_pre \<equiv> ast_action_schema.precondition"
  abbreviation (in ast_domain) "ac_eff \<equiv> ast_action_schema.effect"

  lemma t_ac_name: "ac_name (detype_ac ac) = ac_name ac"
    by (simp add: detype_ac_def)
  lemma t_acs_names: "map ac_name (map detype_ac acs) = map ac_name acs"
    by (simp add: t_ac_name)
  lemma t_acs_dis:
    "distinct (map ac_name (map detype_ac (actions D)))"
    using t_acs_names wf_dom_def by metis

  (* TODO just manipulate lemma  *)
  lemma (in ast_domain) wf_ac_expanded:
    "wf_action_schema a \<longleftrightarrow> (
      let
        tyt = ty_term (map_of (parameters a)) constT
      in
        distinct (map fst (parameters a))
      \<and> wf_fmla tyt (ac_pre a)
      \<and> wf_effect tyt (ac_eff a))"
    using wf_action_schema.simps
    by (metis ast_action_schema.collapse)

  lemma (in ast_domain) t_ac_wf:
    assumes "wf_action_schema a"
    shows "ast_domain.wf_action_schema detype_dom (detype_ac a)"
  proof -
    interpret d2 : ast_domain detype_dom .
    let ?a2 = "detype_ac a"
    define tyt where tyt: "tyt \<equiv> ty_term (map_of (parameters a)) constT"
    from assms have 1: "distinct (map fst (parameters a))" using wf_ac_expanded by metis
    from assms tyt have 2: "wf_fmla tyt (ac_pre a)" using wf_ac_expanded by metis
    from assms tyt have 3: "wf_effect tyt (ac_eff a)" using wf_ac_expanded by metis
  
    define tyt2 where tyt2: "tyt2 \<equiv> ty_term (map_of (parameters ?a2)) d2.constT"
    have ps: "parameters ?a2 = detype_ents (parameters a)" by (simp add: detype_ac_def)
    hence c1: "distinct (map fst (parameters ?a2))" using 1 t_ents_dis by auto
    text \<open>This fact is not required for \<open>wf_action_schema\<close> but it should be, maybe\<close>
    from ps have cx: "(\<forall>(n,T)\<in>set (parameters ?a2). d2.wf_type T)"
      using t_ents_wf by metis
  
    have c2a: "d2.wf_fmla tyt2 (param_precond (parameters a))" sorry
    have c2b: "d2.wf_fmla tyt2 (ac_pre a)" sorry
    from c2a c2b have c2: "d2.wf_fmla tyt2 (ac_pre ?a2)" by (simp add: detype_ac_def)
    have "d2.wf_effect tyt2 (ac_eff a)" sorry
    hence c3: "d2.wf_effect tyt2 (ac_eff ?a2)" by (simp add: detype_ac_def)
  
    from c1 c2 c3 tyt2 show ?thesis using d2.wf_ac_expanded by simp
  qed

  lemma t_acs_wf:
    shows "(\<forall>a\<in>set (map detype_ac (actions D)). ast_domain.wf_action_schema detype_dom a)"
    using detype_dom_def wf_dom_def t_ac_wf by simp

  theorem detype_dom_wf:
    shows "ast_domain.wf_domain detype_dom"
  proof -
    interpret d2 : ast_domain detype_dom .
  
    (* Types are well-formed because they are simply empty. *)
    have c1: "d2.wf_types" using d2.wf_types_def detype_dom_def by simp
    note c2 = t_preds_dis
    note c3 = t_preds_wf
    have "distinct (map fst (consts D))" using wf_dom_def by simp
    hence c4: "distinct (map fst (detype_ents(consts D)))"
      by (simp add: t_ents_dis)
    have c5: "(\<forall>(n,T)\<in>set (detype_ents (consts D)). d2.wf_type T)"
      using t_ents_wf by metis
    have c6: "distinct (map ac_name (map detype_ac (actions D)))"
      using t_acs_dis by simp
    note c7 = t_acs_wf
  
    from c1 c2 c3 c4 c5 c6 c7 show ?thesis
      using d2.wf_domain_def detype_dom_def by simp
  qed
end

(* ---------------------- Milestones ------------------------- *)


(* TODO update locale hierarchy accordingly *)
lemma (in ast_problem) "ast_problem.wf_problem detype_prob"
  oops

lemma "ast_domain.wf_domain D \<Longrightarrow> typeless_dom (detype_dom D)"
  oops

lemma "ast_problem.wf_problem P \<Longrightarrow> typeless_prob (detype_prob P)"
  oops

(* type normalization correct w.r.t. execution*)

lemma (in restr_problem) "valid_plan \<pi> \<Longrightarrow> ast_problem.valid_plan detype_prob \<pi>"
  oops

end