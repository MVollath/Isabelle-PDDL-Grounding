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
    using restrP restrict_prob_def by simp

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

context ast_domain
begin

text \<open> basic stuff \<close>

  lemma (in -) dist_pred: "distinct names \<longleftrightarrow> distinct (map Pred names)"
    by (meson distinct_map inj_onI predicate.inject)

  lemmas (in wf_ast_domain) wf_dom_def = wf_domain[unfolded wf_domain_def]
  
  lemmas (in wf_ast_problem) wf_prob_def = wf_problem[unfolded wf_problem_def]

text \<open> type system \<close>

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

  lemma tyterm_elem: "(ty_term (map_of varT) (map_of cnstT) x \<noteq> None)
    \<longleftrightarrow> (case x of term.VAR x' \<Rightarrow> x' \<in> fst ` set varT |
                   term.CONST x' \<Rightarrow> x' \<in> fst ` set cnstT)"
    apply (split term.split)
    using tyterm_prop by (simp add: map_of_eq_None_iff)

text \<open> type_names \<close>

 lemma wf_type_iff_listed: "wf_type T \<longleftrightarrow> (\<forall>t \<in> set (primitives T). t \<in> set (type_names))"
  proof -
    have "set type_names = insert ''object'' (fst ` set (types D))"  by auto
    hence "wf_type (Either ts) \<longleftrightarrow> (\<forall>t \<in> set ts. t \<in> set (type_names))" for ts
      by (simp add: subset_code(1))
    thus ?thesis using type.collapse by metis
  qed

text \<open> pred_for_type \<close>

  lemma type_preds_ids: "map pred type_preds = map pred_for_type type_names"
    using type_preds_def by simp

  lemma type_pred_refs_type: "p \<in> pred ` set type_preds \<longleftrightarrow> (\<exists>t \<in> set type_names. p = pred_for_type t)"
  proof -
    have "pred ` set type_preds = pred_for_type ` set type_names"
      by (metis type_preds_ids list.set_map)
    thus ?thesis by auto
  qed

text \<open> type_preds \<close>

  lemma tps_dis:
    "distinct (map pred type_preds)" (is "distinct ?tp_ids")
  proof -
    let ?pred_ids = "map pred (predicates D)"
    let ?prefix = "safe_prefix (map predicate.name ?pred_ids)"
    have tp_ids: "?tp_ids = map (Pred \<circ> ((@) ?prefix)) type_names"
        by (simp add: type_preds_ids)
    have "distinct (map ((@) ?prefix) type_names)" (* because: distinct type_names *)
      using dist_prefix by simp
    hence "distinct (map (Pred \<circ> ((@) ?prefix)) type_names)"
      using dist_pred by simp
    thus "distinct ?tp_ids" using tp_ids by metis
  qed

text \<open> supertype preds \<close>

text \<open> supertype facts \<close>

text \<open> type conds/preconds \<close>

text \<open> detyped preds \<close>

  lemma preds_detyped:
    "\<forall>p \<in> set (predicates D2). \<forall>T \<in> set (argTs p). T = \<omega>"
    using type_preds_def detype_preds_def detype_dom_def by auto

  lemma dt_pred_name: "pred (detype_pred pd) = pred pd" by simp

  lemma dt_preds_names:
    "map pred (detype_preds ps) = map pred ps"
    using dt_pred_name detype_preds_def by simp

  (* TODO simplify *)
  lemma tps_dt_preds_disj:
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

  lemma (in wf_ast_domain) t_preds_dis:
    shows "distinct (map pred (predicates D2))"
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

  lemma (in ast_domain2) t_preds_wf:
    "\<forall>p \<in> set (predicates D2). d2.wf_predicate_decl p"
  proof -
    have "\<forall>p \<in> set (predicates D2). \<forall>T \<in> set (argTs p). T = \<omega>"
      by (rule preds_detyped)
    hence "\<forall>p \<in> set (predicates D2). \<forall>T \<in> set (argTs p). d2.wf_type T"
      using preds_detyped wf_object by auto
    thus ?thesis by (metis d2.wf_predicate_decl.simps predicate_decl.collapse)
  qed

text \<open> detype ents \<close>

  lemma ents_detyped: "\<forall>(n, T) \<in> set (detype_ents ents). T = \<omega>"
    by (simp add: detype_ents_def case_prod_beta' detype_dom_def)

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
    have 1: "\<forall>T \<in> snd ` set (detype_ents ents). T = \<omega>" using ents_detyped by fastforce
    have "map_of ents x \<noteq> None \<longleftrightarrow> x \<in> fst ` set ents" using map_of_eq_None_iff by metis
    also have "... \<longleftrightarrow> x \<in> fst ` set (detype_ents ents)" using t_ents_names by (metis list.set_map)
    
    ultimately show ?thesis using 1 map_of_in_R_iff
      by (metis map_of_eq_None_iff option.discI)
  qed

  lemma t_entT_None:
    shows "map_of ents x = None \<longleftrightarrow> map_of (detype_ents ents) x = None"
    using t_ents_names list.set_map map_of_eq_None_iff by metis

text \<open> predicate signatures \<open>sig\<close> \<close>

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

  lemma (in wf_ast_domain) sig_some:
    "sig p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set (predicates D)"
  proof -
    have "distinct (map pred (predicates D))" using wf_dom_def by simp
    thus ?thesis using pred_resolve sig_def by simp
  qed

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
  lemma (in wf_ast_domain2) t_sig_split_b:
    "d2.sig =
      map_of (map split_pred type_preds) ++ map_of (map split_pred (detype_preds (predicates D)))"
  proof -
    have dis: "distinct (map pred (predicates D))" using wf_dom_def by simp

    let ?pred_map2 = "(map split_pred (predicates D2))"
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

  lemma (in wf_ast_domain2) t_sig_some:
    "d2.sig p \<noteq> None \<longleftrightarrow>
      (p \<in> pred ` set (predicates D))
      \<or> (p \<in> pred_for_type ` set type_names)"
  proof -
    have dis: "distinct (map pred (predicates D))" using wf_dom_def by simp

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
      using type_preds_ids dt_preds_names by simp_all
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
    have dis: "distinct (map pred (predicates D))" using wf_dom_def by simp
    let ?dt_pred_map = "map split_pred (detype_preds (predicates D))"

    have "PredDecl p Ts \<in> set (predicates D)" using assms sig_some by simp
    hence "PredDecl p (replicate (length Ts) \<omega>) \<in> set (detype_preds (predicates D))"
      using detype_preds_def by force
    hence "map_of ?dt_pred_map p = Some (replicate (length Ts) \<omega>)" using pred_resolve
      using dis dt_preds_names by force
    thus ?thesis using t_sig_split_b by simp
  qed


text \<open> type maps \<close>

  lemma (in ast_domain2) t_constT_Some: "constT c \<noteq> None \<longleftrightarrow> d2.constT c = Some \<omega>"
    using t_entT_Some ast_domain.constT_def detype_dom_def by fastforce

  lemma (in ast_domain2) t_constT_None: "constT c = None \<longleftrightarrow> d2.constT c = None"
    using t_entT_None ast_domain.constT_def detype_dom_def by fastforce

  lemma (in ast_problem2) t_objT_Some: "objT c \<noteq> None \<longleftrightarrow> p2.objT c = Some \<omega>"
  proof -
    have "objT c \<noteq> None \<longleftrightarrow> constT c \<noteq> None \<or> constT c = None \<and> map_of (objects P) c \<noteq> None"
      using objT_def by auto
    also have "... \<longleftrightarrow> constT c \<noteq> None \<or> constT c = None \<and> map_of (objects detype_prob) c = Some \<omega>"
      using detype_prob_def t_entT_Some by fastforce
    also have "... \<longleftrightarrow> p2.constT c = Some \<omega> \<or> constT c = None \<and> map_of (objects detype_prob) c = Some \<omega>"
      using detype_prob_def t_constT_Some by fastforce
    also have "... \<longleftrightarrow> p2.constT c = Some \<omega> \<or> p2.constT c = None \<and> map_of (objects detype_prob) c = Some \<omega>"
      using detype_prob_def t_constT_None by fastforce
    also have "... \<longleftrightarrow> (map_of (objects detype_prob) ++ p2.constT) c = Some \<omega>"
      using map_add_Some_iff by fastforce
    also have "... \<longleftrightarrow> p2.objT c = Some \<omega>" using p2.objT_def by simp
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
    have b: "d2.sig p = Some ?os" using sigp by (simp add: t_preds_arity)

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
    using wf_effect.simps ast_effect.collapse
    by metis (* TODO how to just manipulate this lemma with options? *)

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

  lemma ac_params_detyped:
    "\<forall>ac \<in> set (actions D2). \<forall>(n, T) \<in> set (parameters ac). T = \<omega>"
    using detype_dom_def detype_ac_def ents_detyped by fastforce

  abbreviation "ac_name \<equiv> ast_action_schema.name"
  (* abbreviation (in ast_domain) "ac_params \<equiv> ast_action_schema.parameters" \<comment> just use \<open>parameters\<close> *)
  abbreviation "ac_pre \<equiv> ast_action_schema.precondition"
  abbreviation "ac_eff \<equiv> ast_action_schema.effect"

  lemma t_ac_name: "ac_name (detype_ac ac) = ac_name ac"
    by (simp add: detype_ac_def)
  lemma t_acs_names: "map ac_name (map detype_ac acs) = map ac_name acs"
    by (simp add: t_ac_name)
  lemma (in wf_ast_domain) t_acs_dis:
    "distinct (map ac_name (map detype_ac (actions D)))"
    using t_acs_names wf_dom_def by metis

  (* TODO just manipulate lemma  *)
  lemma wf_ac_expanded:
    "wf_action_schema a \<longleftrightarrow> (
      let
        tyt = ty_term (map_of (parameters a)) constT
      in
        distinct (map fst (parameters a))
      \<and> wf_fmla tyt (ac_pre a)
      \<and> wf_effect tyt (ac_eff a))"
    using wf_action_schema.simps
    by (metis ast_action_schema.collapse)

  lemma (in ast_domain2) t_ac_tyt:
    assumes "ty_term (map_of (parameters a)) constT x \<noteq> None"
    shows "ty_term (map_of (parameters (detype_ac a))) d2.constT x = Some \<omega>"
    using assms detype_ac_def detype_dom_def t_tyt_Some ast_domain.constT_def by auto

  lemma params_ts_wf:
    assumes "wf_action_params a" "p \<in> set (parameters a)"
    shows "wf_type (snd p)"
    using assms wf_action_params_def by blast

  lemma params_ts_exist: (* somehow this isn't trivial for the solver *)
    assumes "wf_action_params a" "p \<in> set (parameters a)"
    shows "\<forall>t \<in> set (primitives (snd p)). t \<in> insert ''object'' (set type_names)"
    using assms params_ts_wf
    by (metis wf_type_iff_listed insertI2)

  lemma (in wf_ast_domain2) type_precond_wf: (* TODO simplify if possible *)
    assumes "wf_action_params a" "p \<in> set (parameters a)"
    shows "d2.wf_fmla
      (ty_term (map_of (parameters (detype_ac a))) cnstT)
      (type_precond p)"
  proof -
    let ?tyt = "ty_term (map_of (parameters a)) cnstT"
    let ?tyt2 = "ty_term (map_of (parameters (detype_ac a))) cnstT"

    have "?tyt (term.VAR (fst p)) \<noteq> None" using assms detype_ac_def
      by (metis imageI map_of_eq_None_iff ty_term.simps(1))
    hence 1: "?tyt2 (term.VAR (fst p)) = Some \<omega>" using t_tyt_var_Some
      by (simp add: detype_ac_def)

    have "\<forall>t \<in> set (primitives (snd p)). d2.wf_fmla ?tyt2 (Atom (predAtm (pred_for_type t) [term.VAR (fst p)]))"
    proof
      fix t assume t: "t \<in> set (primitives (snd p))"
      have "t \<in> insert ''object'' (set type_names)" using assms params_ts_exist t by simp
      hence "PredDecl (pred_for_type t) [\<omega>] \<in> set type_preds" using type_preds_def by fastforce
      moreover have "set type_preds \<subseteq> set (predicates D2)" using detype_dom_def by simp
      ultimately have "PredDecl (pred_for_type t) [\<omega>] \<in> set (predicates D2)" by auto
      hence 2: "d2.sig (pred_for_type t) = Some [\<omega>]" using detype_dom_def
        by (metis d2.sig_def pred_resolve t_preds_dis) (* not true outside of restr_dom because action params need not wf *)
      from 1 2 show "d2.wf_fmla ?tyt2 (Atom (predAtm (pred_for_type t) [term.VAR (fst p)]))"
        using d2.of_type_refl d2.is_of_type_def by fastforce
    qed

    hence "\<forall>\<phi> \<in> set (map (Atom \<circ> (\<lambda>pn. predAtm pn [term.VAR (fst p)])) (type_conds (snd p))). d2.wf_fmla ?tyt2 \<phi>"
      by simp
    hence "d2.wf_fmla ?tyt2 (disj_fmlas (map (Atom \<circ> (\<lambda>pn. predAtm pn [term.VAR (fst p)])) (type_conds (snd p))))"
      using d2.disj_fmlas_wf by metis
    thus "d2.wf_fmla ?tyt2 (type_precond p)"
      by (metis prod.collapse type_precond.simps)
  qed

  lemma (in wf_ast_domain2) t_param_precond_wf:
    assumes "wf_action_params a"
    shows "d2.wf_fmla
    (ty_term (map_of (parameters (detype_ac a))) egal)
    (param_precond (parameters a))"
  proof -
    let ?tyt2 = "ty_term (map_of (parameters (detype_ac a))) egal"
    have "param_precond (parameters a) = conj_fmlas (map type_precond (parameters a))"
      by simp
    have "\<forall>p \<in> set (parameters a). d2.wf_fmla
      ?tyt2
      (type_precond p)" using type_precond_wf assms by simp
    hence "\<forall>\<phi> \<in> set (map type_precond (parameters a)). d2.wf_fmla ?tyt2 \<phi>" by simp
    hence "d2.wf_fmla ?tyt2 (conj_fmlas (map type_precond (parameters a)))"
      using d2.conj_fmlas_wf by blast
    thus ?thesis by simp
  qed

  lemma (in restr_domain2) t_ac_wf:
    assumes "a \<in> set (actions D)"
    shows "d2.wf_action_schema (detype_ac a)"
  proof -
    let ?a2 = "detype_ac a"
    let ?tyt = "ty_term (map_of (parameters a)) constT"
    let ?tyt2 = "ty_term (map_of (parameters (detype_ac a))) d2.constT"
    have tyt_om: "\<forall>x. ?tyt x \<noteq> None \<longrightarrow> ?tyt2 x = Some \<omega>" using t_ac_tyt by simp

    from assms have wfa: "wf_action_schema a" using wf_domain wf_domain_def by simp
    from assms have "distinct (map fst (parameters a))" using wfa wf_ac_expanded by metis
    hence c1: "distinct (map fst (parameters ?a2))" using t_ents_dis detype_ac_def by auto
    from assms have "wf_fmla ?tyt (ac_pre a)" using wfa wf_ac_expanded by metis
    hence c2b: "d2.wf_fmla ?tyt2 (ac_pre a)" using tyt_om t_fmla_wf by blast
    from assms have "wf_effect ?tyt (ac_eff a)" using wfa wf_ac_expanded by metis
    hence "d2.wf_effect ?tyt2 (ac_eff a)"
      using tyt_om ast_domain.wf_effect.simps t_eff_wf detype_ac_def by blast
    hence c3: "d2.wf_effect ?tyt2 (ac_eff ?a2)" using detype_ac_def by simp

    have "wf_action_params a" using restrD restrict_dom_def assms by simp
    note c2a = t_param_precond_wf[OF this]
    from c2a c2b have c2: "d2.wf_fmla ?tyt2 (ac_pre ?a2)" by (simp add: detype_ac_def)

    from c1 c2 c3 show ?thesis using d2.wf_ac_expanded by simp
  qed

  lemma (in restr_domain2) t_acs_wf:
    shows "(\<forall>a\<in>set (map detype_ac (actions D)). d2.wf_action_schema a)"
    using detype_dom_def wf_dom_def t_ac_wf by simp

text \<open> init / goal \<close>

lemma (in wf_ast_problem) t_init_dis: "distinct (init P2)"
proof -
  have "init P2 = supertype_facts (objects P) @ supertype_facts (consts D) @ (init P)"
    using detype_prob_def by simp
  show ?thesis sorry
qed
  
lemma (in wf_ast_problem2) t_init_wf:
  "p2.wf_world_model (set (init P2))"
  sorry


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

  theorem (in restr_problem2) detype_prob_wf:
    shows "p2.wf_problem"
  proof -
    note c1 = detype_dom_wf
    have "distinct (map fst (objects P) @ map fst (consts D))" using wf_prob_def by simp
    hence c2: "distinct (map fst (detype_ents (objects P)) @ map fst (detype_ents (consts D)))"
      using t_ents_names by metis
    have c3: "\<forall>(n, y)\<in>set (objects P2). p2.wf_type y"
      using t_ents_wf detype_prob_def by fastforce
    note c4 = t_init_dis
    note c5 = t_init_wf
  
    have c6a: "\<forall>e. objT e \<noteq> None \<longrightarrow> p2.objT e = Some \<omega>" using t_objT_Some by simp
    have c6b: "wf_fmla objT (goal P2)" using detype_prob_def wf_prob_def by simp
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

(* ---------------------- Future Milestones ------------------------- *)

(* type normalization correct w.r.t. execution*)

lemma (in restr_problem) "valid_plan \<pi> \<Longrightarrow> ast_problem.valid_plan detype_prob \<pi>"
  oops

end