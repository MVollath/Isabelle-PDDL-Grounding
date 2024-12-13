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
    apply unfold_locales
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
    apply unfold_locales
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

(* This is mostly to simplify the syntax, actually. So I can just do
   \<open>Dt.some_function\<close> instead of \<open>ast_domain.some_function detype_dom\<close> *)
locale ast_domain2 = ast_domain
sublocale ast_domain2 \<subseteq> Dt: ast_domain detype_dom .
locale wf_ast_domain2 = wf_ast_domain
sublocale wf_ast_domain2 \<subseteq> Dt: ast_domain detype_dom .

locale ast_problem2 = ast_problem
sublocale ast_problem2 \<subseteq> Pt: ast_problem detype_prob .

subsection \<open>Type Normalization Proofs\<close>

subsubsection \<open> Type Normalization Produces Typeless PDDL \<close>

lemma (in ast_domain) preds_detyped: "\<forall>p \<in> set (predicates detype_dom). \<forall>T \<in> set (argTs p). T = \<omega>"
  using type_preds_def detype_preds_def detype_dom_def by auto

lemma (in ast_domain) ents_detyped: "\<forall>(n, T) \<in> set (detype_ents ents). T = \<omega>"
  unfolding detype_ents_def
  by (simp add: case_prod_beta' detype_dom_def)

lemma (in ast_domain) ac_params_detyped:
  "\<forall>ac \<in> set (actions detype_dom). \<forall>(n, T) \<in> set (parameters ac). T = \<omega>"
  using detype_dom_def detype_ac_def ents_detyped by fastforce

lemma (in restr_domain) dom_detyped:
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

lemma (in restr_problem) prob_detyped:
  "ast_problem.typeless_prob detype_prob"
proof -
  have "\<forall>(n, T) \<in> set (objects detype_prob). T = \<omega>"
    by (simp add: detype_prob_def ents_detyped)
  thus ?thesis using dom_detyped ast_problem.typeless_prob_def detype_prob_def by simp
qed

subsubsection \<open> Type Normalization Preserves Well-Formedness \<close>

(* Properties of Ab+La *)

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

  (* signatures *)
  
  lemma sig_none: "sig p \<noteq> None \<longleftrightarrow> p \<in> pred ` set (predicates D)"
  proof -
    have "sig p = map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates D)) p"
      using sig_def by simp
    have "sig p \<noteq> None \<longleftrightarrow> p \<in> fst ` set (map (\<lambda>PredDecl p n \<Rightarrow> (p, n)) (predicates D))"
      by (metis map_of_eq_None_iff sig_def)
    also have "... \<longleftrightarrow> p \<in> pred ` set (predicates D)"
      by (simp add: image_iff predicate_decl.case_eq_if)
    finally show ?thesis .
  qed
end

context wf_ast_domain
begin
  (* Deliberate shortcut: The goal is explaining that if a predatm in the original problem is well-
  formed, so is the corresponding predatm in the detyped problem. I use distincness of predicate IDs
  as an assumption here, to make the map_of logic simpler. But technically this isn't really
  necessary. TODO explain, maybe *)
  lemma pred_resolve:
    shows "map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p, n)) (predicates D)) p = Some Ts
      \<longleftrightarrow> PredDecl p Ts \<in> set (predicates D)"
  proof -
    define preds where ps: "preds \<equiv> predicates D"
    hence dis: "distinct (map pred preds)" using wf_domain wf_domain_def by simp
    let ?map = "map (\<lambda>pd. (pred pd, argTs pd)) preds"
    have zip: "?map = zip (map pred preds) (map argTs preds)"
      by (induction preds) simp_all
    hence "map_of ?map p = Some Ts \<longleftrightarrow> (p, Ts) \<in> set ?map" using dis by simp
    also have "... \<longleftrightarrow> PredDecl p Ts \<in> set preds" by force
    ultimately show ?thesis
      by (simp add: predicate_decl.case_eq_if ps)
  qed

  lemma sig_some:
    "sig p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set (predicates D)"
    using wf_domain wf_domain_def sig_def pred_resolve by presburger

  lemma sig_E:
    assumes "sig p = Some Ts"
    shows "\<exists>!i. i < length (predicates D) \<and> (predicates D ! i = PredDecl p Ts)"
    oops
end

context ast_domain begin
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

lemma dist_pred: "distinct names \<Longrightarrow> distinct (map Pred names)"
  by (meson distinct_map inj_onI predicate.inject)

context wf_ast_domain
begin
  lemmas wf_dom_def = wf_domain[unfolded wf_domain_def]

  lemma (in ast_domain) t_pred_name: "pred pd = pred (detype_pred pd)" by simp

  lemma t_preds_names: (* TODO simplify *)
    shows "distinct (map pred (predicates detype_dom))"
  proof -
    (* Predicate names are unique because the original predicate names are unchanged
       and the additional predicate names are unique (based on unique type names)
       and distinct from the original predicates. *)
    let ?preds = "map pred (predicates D)"
    let ?t_preds = "map pred type_preds"
    let ?dt_preds = "map pred (detype_preds (predicates D))"

    have dis: "distinct (map pred (predicates D))" using wf_dom_def by simp
    have p_eq_dt: "?preds = ?dt_preds" using t_pred_name detype_preds_def by simp
    hence g1: "distinct ( map pred (detype_preds (predicates D)))"
      using dis by argo
  
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
    ultimately have g2: "set ?t_preds \<inter> set ?dt_preds = {}" by (metis p_eq_dt)
    
    have d: "distinct (map ((@) ?prefix) type_names)" (* fact: distinct type_names *)
      using dist_prefix by simp
    hence "distinct (map (Pred \<circ> ((@) ?prefix)) type_names)"
      using dist_pred[OF d] by simp
    hence g3: "distinct (?t_preds)" using t_ps_expand by metis
  
    from g1 g2 g3 have "distinct (map pred (type_preds @ detype_preds (predicates D)))" by simp
    thus ?thesis using ast_domain.sel(2) detype_dom_def by presburger
  qed

  lemma (in ast_domain2) t_preds_wf2:
    "\<forall>p \<in> set (predicates detype_dom). Dt.wf_predicate_decl p"
  proof -
    have "\<forall>p \<in> set (predicates detype_dom). \<forall>T \<in> set (argTs p). T = \<omega>"
      by (rule preds_detyped)
    hence "\<forall>p \<in> set (predicates detype_dom). \<forall>T \<in> set (argTs p). Dt.wf_type T"
      using preds_detyped wf_object by auto
    thus ?thesis by (metis Dt.wf_predicate_decl.simps predicate_decl.collapse)
  qed


lemma (in ast_domain) t_preds_wf:
    "\<forall>p \<in> set (predicates detype_dom). ast_domain.wf_predicate_decl detype_dom p"
  using ast_domain2.t_preds_wf2 .

  lemma (in ast_domain) t_ents_names:
    assumes "distinct (map fst ents)"
    shows "distinct (map fst (detype_ents ents))"
  proof -
    have "\<And>xs. map fst xs = map fst (map detype_ent xs)" by auto
    thus ?thesis using assms by (metis detype_ents_def)
  qed

  lemma (in ast_domain) t_ents_wf:
    shows "(\<forall>(n,T)\<in>set (detype_ents ents). ast_domain.wf_type detype_dom T)"
    using ents_detyped wf_object by fast

(* formulas *)

(* Detyped formulas *)
  lemma "ast_domain.constT d x = None \<longleftrightarrow> (x \<notin> fst ` set (consts d))"
    using ast_domain.constT_def by (simp add: map_of_eq_None_iff)
  lemma "ast_domain.constT detype_dom x = Some \<omega> \<longleftrightarrow> (x \<in> fst ` set (consts detype_dom))"
    oops

  lemma "argTs (detype_pred p) = replicate (length (argTs p)) \<omega>" by simp
  lemma "map_of (uno @ dos) = map_of dos ++ map_of uno" by simp
  lemma "distinct (map fst uno) \<Longrightarrow> distinct (map fst dos) \<Longrightarrow>
    map_of dos ++ map_of uno = map_of uno ++ map_of dos" sorry
  lemma "funo = zip (map fst uno) (map (f \<circ> snd) uno)
    \<Longrightarrow> map_of uno x = Some y \<Longrightarrow> map_of funo x = Some (f y)" sorry
  (* Prove via: obtain minimal i s.t. x = fst (uno ! i),
     then y = snd (uno ! i), and f y = snd (funo ! i)
     then, since i is minimal, map_of funo x = snd (funo ! i) *)
  lemma "map_of m x \<noteq> None \<longleftrightarrow> (\<exists>p \<in> set m. fst p = x)"
    by (metis fst_conv image_eqI in_fst_imageE map_of_eq_None_iff)
  value "map_of [(1::nat, 1::nat), (1::nat, 2::nat)] 1"
  lemma "map_of m x = Some y \<longleftrightarrow> (i < length m \<and> fst (m ! i) = x \<and>
        snd (m ! i) = y \<and> \<not>(\<exists>j. j < i \<and> fst (m ! j) = x))" oops

  (* map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates D)) *)

  (* using distinctness of predicates is a shortcut here*)
  lemma t_preds_arity:
    assumes "sig p = Some Ts"
    shows "ast_domain.sig detype_dom p
      = Some (replicate (length Ts) \<omega>)"
  proof -
    have "distinct (map pred (predicates D))" using wf_dom_def by simp
    hence "PredDecl p Ts \<in> set (predicates D)" using assms sig_some by blast
    have "predicates detype_dom = type_preds @
      map (\<lambda>pd. PredDecl (pred pd) (replicate (length (argTs pd)) \<omega>)) (predicates D)"
      using detype_dom_def detype_preds_def by simp
    from assms have "distinct (map pred (predicates detype_dom))"
      using t_preds_names by simp
    thus ?thesis sorry
  qed

  (* I feel like I need to figure out how to make my formulas smaller *)
  lemma (in ast_domain)
    assumes "wf_pred_atom (ty_term (map_of params) constT) (p,vs)"
    defines "D2 \<equiv> detype_dom"
    shows "ast_domain.wf_pred_atom D2 (ty_term (map_of (detype_ents params)) (ast_domain.constT D2)) (p,vs)"
  proof -
    interpret d2 : ast_domain detype_dom .
    let ?tyt = "ty_term (map_of params) constT"
    let ?tyt2 = "ty_term (map_of (detype_ents params)) d2.constT"
    
    from assms obtain Ts where "sig p = Some Ts \<and> list_all2 (is_of_type ?tyt) vs Ts"
      by (metis not_None_eq option.simps(4-5) wf_pred_atom.simps)
    hence "length vs = length Ts" using list_all2_lengthD by auto
    oops


  (* ty_term (map_of params) constT *)

  (* fun wf_pred_atom_c :: "ast_domain \<Rightarrow> ('ent \<rightharpoonup> type) \<Rightarrow> predicate \<times> 'ent list \<Rightarrow> bool" where
    "wf_pred_atom_c D ty_ent (p,vs) \<longleftrightarrow> (
      case (sig_c D) p of
        None \<Rightarrow> False
      | Some Ts \<Rightarrow> list_all2 (is_of_type_c D ty_ent) vs Ts)" *)

  (* actions *)
  abbreviation (in ast_domain) "ac_name \<equiv> ast_action_schema.name"
  (* abbreviation (in ast_domain) "ac_params \<equiv> ast_action_schema.parameters" -- just use \<open>parameters\<close> *)
  abbreviation (in ast_domain) "ac_pre \<equiv> ast_action_schema.precondition"
  abbreviation (in ast_domain) "ac_eff \<equiv> ast_action_schema.effect"

  lemma t_acs_names:
    shows "distinct (map ac_name (map detype_ac (actions D)))"
  proof -
    have dis: "distinct (map ac_name (actions D))"
      using wf_dom_def by simp
    have "map ac_name (actions D) = map ac_name (map detype_ac (actions D))"
      by (simp add: detype_ac_def)
    thus ?thesis using dis by argo
  qed

  (* wf type not checked! *)
  (* fun wf_action_schema :: "ast_action_schema \<Rightarrow> bool" where
    "wf_action_schema (Action_Schema n params pre eff) \<longleftrightarrow> (
      let
        tyt = ty_term (map_of params) constT
      in
        distinct (map fst params)
      \<and> wf_fmla tyt pre
      \<and> wf_effect tyt eff)" *)

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

  lemma (in ast_domain) t_acs_wf_aux:
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
    hence c1: "distinct (map fst (parameters ?a2))" using 1 t_ents_names by auto
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
  proof -
    interpret d2 : ast_domain detype_dom .
    have wf_acs: "\<forall>a\<in>set (actions D). wf_action_schema a" using wf_dom_def by simp
    oops

  theorem detype_dom_wf:
    shows "ast_domain.wf_domain detype_dom"
  proof -
    interpret d2 : ast_domain detype_dom .
  
    (* Types are well-formed because they are simply empty. *)
    have c1: "d2.wf_types" using d2.wf_types_def detype_dom_def by simp
    note c2 = t_preds_names
    note c3 = t_preds_wf
    have "distinct (map fst (consts D))" using wf_dom_def by simp
    hence c4: "distinct (map fst (detype_ents(consts D)))"
      by (simp add: t_ents_names)
    have c5: "(\<forall>(n,T)\<in>set (detype_ents (consts D)). d2.wf_type T)"
      using t_ents_wf by metis
    have c6: "distinct (map ac_name (map detype_ac (actions D)))"
      using t_acs_names by simp
    have c7: "(\<forall>a\<in>set (map detype_ac (actions D)). d2.wf_action_schema a)" sorry
  
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