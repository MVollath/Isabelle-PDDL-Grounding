theory PDDL_Normalization_old
  imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    Graph_Funs String_Shenanigans
begin

text \<open>TODO: Even before performing normalization, we place a few restrictions on the input PDDL task.
Some of these aren't strictly necessary and will only be kept in place for the MVP.\<close>

text \<open>Check if a formula consists of only (nested) conjunctions of literals.\<close>
fun only_conj :: "'a formula \<Rightarrow> bool" where
  "only_conj (Atom a) \<longleftrightarrow> True" |
  "only_conj \<bottom> \<longleftrightarrow> True" |
  "only_conj (\<^bold>\<not> (Atom a)) \<longleftrightarrow> True" |
  "only_conj (\<phi> \<^bold>\<and> \<psi>) \<longleftrightarrow> only_conj \<phi> \<and> only_conj \<psi>" |

  "only_conj (\<^bold>\<not> _) \<longleftrightarrow> False" |
  "only_conj (_ \<^bold>\<or> _) \<longleftrightarrow> False" |
  "only_conj (_ \<^bold>\<rightarrow> _) \<longleftrightarrow> False"

subsection \<open> Type Normalization \<close>
abbreviation "type_names D \<equiv> remdups (''object'' # map fst (types D))"

abbreviation singleton_types :: "('a \<times> type) list \<Rightarrow> bool" where
  "singleton_types os \<equiv> (\<forall>(_, t) \<in> set os. length (primitives t) = 1)"

definition const_single_types :: "ast_domain \<Rightarrow> bool" where
  "const_single_types D \<equiv> singleton_types (consts D)"

definition objs_single_types :: "ast_problem \<Rightarrow> bool" where
  ost_aux: "objs_single_types P \<equiv>
    const_single_types (domain P)
    \<and> singleton_types (objects P)"

definition restricted_pddl :: "ast_problem \<Rightarrow> bool" where
  "restricted_pddl P \<longleftrightarrow> objs_single_types P"

definition pred_names :: "ast_domain \<Rightarrow> name list" where
  "pred_names D = map (predicate.name \<circ> pred) (predicates D)"

fun pred_for_type :: "ast_domain \<Rightarrow> name \<Rightarrow> predicate" where
  "pred_for_type D t = Pred (safe_prefix (pred_names D) @ t)"

fun type_preds :: "ast_domain \<Rightarrow> predicate_decl list" where
  "type_preds D = map ((\<lambda>p. PredDecl p [Either [''object'']]) \<circ> (pred_for_type D)) (type_names D)"

fun supertype_preds :: "ast_domain \<Rightarrow> name \<Rightarrow> predicate list" where
  "supertype_preds D t = map (pred_for_type D) (reachable_nodes (types D) t)"

text \<open>This only works for singleton types on purpose.\<close>
fun supertype_facts_for :: "ast_domain \<Rightarrow> (object \<times> type) \<Rightarrow> object atom formula list" where
  "supertype_facts_for D (n, Either [t]) =
    map (Atom \<circ> (\<lambda>p. predAtm p [n])) (supertype_preds D t)"

fun type_conds :: "ast_domain \<Rightarrow> type \<Rightarrow> predicate list" where
  "type_conds D (Either ts) = map (pred_for_type D) ts"

fun disj_fmlas :: "'a formula list \<Rightarrow> 'a formula" where
  "disj_fmlas [] = Bot" |
  "disj_fmlas [f] = f" |
  "disj_fmlas (f # fs) = f \<^bold>\<or> disj_fmlas fs"

fun conj_fmlas :: "'a formula list \<Rightarrow> 'a formula" where
  "conj_fmlas [] = \<^bold>\<not> \<bottom>" |
  "conj_fmlas [f] = f" |
  "conj_fmlas (f # fs) = f \<^bold>\<and> conj_fmlas fs"

fun type_precond :: "ast_domain \<Rightarrow> (variable \<times> type) \<Rightarrow> term atom formula" where
  "type_precond D (v, T) =
    disj_fmlas (map (Atom \<circ> (\<lambda>p. predAtm p [term.VAR v])) (type_conds D T))"

fun param_precond :: "ast_domain \<Rightarrow> (variable \<times> type) list \<Rightarrow> term atom formula" where
  "param_precond D params = conj_fmlas (map (type_precond D) params)"

fun detype_ent :: "('ent \<times> type) \<Rightarrow> ('ent \<times> type)" where
  "detype_ent (n, T) = (n, Either [''object''])"

definition detype_ents :: "('ent \<times> type) list \<Rightarrow> ('ent \<times> type) list" where
  "detype_ents params \<equiv> map detype_ent params"

fun detype_ac :: "ast_domain \<Rightarrow> ast_action_schema \<Rightarrow> ast_action_schema" where
  "detype_ac D (Action_Schema nam params pre eff) =
    Action_Schema nam (detype_ents params) (param_precond D params \<^bold>\<and> pre) eff"

fun detype_preds :: "predicate_decl list \<Rightarrow> predicate_decl list" where
  "detype_preds preds =
    map (\<lambda>pd. PredDecl (pred pd) (replicate (length (argTs pd)) (Either [''object'']))) preds"

fun detype_dom :: "ast_domain \<Rightarrow> ast_domain" where
  "detype_dom D =
    Domain
      []
      (type_preds D @ detype_preds (predicates D))
      (detype_ents (consts D))
      (map (detype_ac D) (actions D))"

fun supertype_facts :: "ast_domain \<Rightarrow> (object \<times> type) list \<Rightarrow> object atom formula list" where
  "supertype_facts D objs = concat (map (supertype_facts_for D) objs)"

fun detype_prob :: "ast_problem \<Rightarrow> ast_problem" where
  "detype_prob (Problem d objs i g) =
    Problem
      (detype_dom d)
      (detype_ents objs)
      (supertype_facts d objs @ supertype_facts d (consts d) @ i)
      g"

definition typeless_dom :: "ast_domain \<Rightarrow> bool" where
  "typeless_dom D = undefined"

definition typeless_prob :: "ast_problem \<Rightarrow> bool" where
  "typeless_prob P = undefined"

subsection \<open>Complete Normalization\<close>

definition normalized_prob :: "ast_problem \<Rightarrow> bool" where
  "normalized_prob P \<equiv> typeless_prob P \<and> undefined"

(* ------------------------------------- PROOFS ------------------------------------------------- *)

(* properties of Ab+La *)

lemma subtype_edge_swap: "ast_domain.subtype_edge = prod.swap"
proof -
  have "\<And>a b. ast_domain.subtype_edge (a, b) = prod.swap (a, b)"
    by (simp add: ast_domain.subtype_edge.simps)
  thus ?thesis by fast
qed

lemma wf_object: "ast_domain.wf_type D (Either [''object''])"
  unfolding ast_domain.wf_type.simps by simp

(* ty_term. I might be really bad at Isabelle*)
lemma tyterm_simp: "(ty_term varT cnstT x) =
  (case x of term.VAR x' \<Rightarrow> varT x' |
                 term.CONST x' \<Rightarrow> cnstT x')"
  apply (auto split: term.split)
  done

lemma tyterm_prop: "P (ty_term varT cnstT x) \<longleftrightarrow>
  (case x of term.VAR x' \<Rightarrow> P (varT x') |
                 term.CONST x' \<Rightarrow> P (cnstT x'))"
  by (metis tyterm_simp term.case_distrib)

lemma tyterm_elem: "(ty_term (map_of varT) (map_of cnstT) x \<noteq> None)
  \<longleftrightarrow> (case x of term.VAR x' \<Rightarrow> x' \<in> fst ` set varT |
                 term.CONST x' \<Rightarrow> x' \<in> fst ` set cnstT)"
proof -
  have 1: "(ty_term (map_of varT) (map_of cnstT) x \<noteq> None)
  \<longleftrightarrow> (case x of term.VAR x' \<Rightarrow> map_of varT x' \<noteq> None |
                 term.CONST x' \<Rightarrow> map_of cnstT x' \<noteq> None)"
    using tyterm_prop[where P = "\<lambda>x. x\<noteq>None"] by simp
  thus ?thesis
    using map_of_eq_None_iff[of cnstT] map_of_eq_None_iff[of varT] by presburger
qed

(* signatures *)

lemma sig_none: "ast_domain.sig D p \<noteq> None \<longleftrightarrow> p \<in> pred ` set (predicates D)"
proof -
  have "ast_domain.sig D p = map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates D)) p"
    using ast_domain.sig_def by simp
  have "ast_domain.sig D p \<noteq> None \<longleftrightarrow>
    map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p, n)) (predicates D)) p \<noteq> None"
    using ast_domain.sig_def by simp
  also have "... \<longleftrightarrow> p \<in> fst ` set (map (\<lambda>PredDecl p n \<Rightarrow> (p, n)) (predicates D))"
    by (metis map_of_eq_None_iff)
  also have "... \<longleftrightarrow> p \<in> pred ` set (predicates D)"
    by (simp add: image_iff predicate_decl.case_eq_if)
  finally show ?thesis .
qed

(* Deliberate shortcut: The goal is explaining that if a predatm in the original problem is well-
formed, so is the corresponding predatm in the detyped problem. I use distincness of predicate IDs
as an assumption here, to make the map_of logic simpler. But technically this isn't really
necessary. TODO explain, maybe *)
lemma pred_resolve:
  assumes "distinct (map pred preds)"
  shows "map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p, n)) preds) p = Some Ts
    \<longleftrightarrow> PredDecl p Ts \<in> set preds"
proof -
  let ?map = "map (\<lambda>P. (pred P, argTs P)) preds"
  have zip: "?map = zip (map pred preds) (map argTs preds)"
    by (induction preds) simp_all
  hence "map_of ?map p = Some Ts \<longleftrightarrow> (p, Ts) \<in> set ?map" using assms by simp
  also have "... \<longleftrightarrow> PredDecl p Ts \<in> set preds" by force
  ultimately show ?thesis
    by (simp add: predicate_decl.case_eq_if)
qed

lemma sig_some:
  assumes "distinct (map pred (predicates D))"
  shows "ast_domain.sig D p = Some Ts \<longleftrightarrow> PredDecl p Ts \<in> set (predicates D)"
  using assms ast_domain.sig_def pred_resolve by presburger

lemma sig_E:
  assumes "ast_domain.sig D p = Some Ts"
  obtains i where "i < length (predicates D)" "predicates D ! i = PredDecl p Ts"
  oops

(* supertype enumeration *)

lemma wf_type_iff_listed: "ast_domain.wf_type D (Either ts) \<longleftrightarrow> (\<forall>t \<in> set ts. t \<in> set (type_names D))"
proof -
  have "set (type_names D) = insert ''object'' (fst ` set (types D))" by auto
  thus ?thesis by (simp add: ast_domain.wf_type.simps subset_code(1))
qed

lemma of_type_iff_reach:
  shows "ast_domain.of_type D oT T \<longleftrightarrow> (
    \<forall>ot \<in> set (primitives oT).
    \<exists>t \<in> set (primitives T).
      t \<in> set (reachable_nodes (types D) ot))"
proof -
  have "ast_domain.subtype_rel D = set (map prod.swap (types D))"
    using ast_domain.subtype_rel_def subtype_edge_swap by metis
  hence subrel_inv: "ast_domain.subtype_rel D = (set (types D))\<inverse>" by auto
  hence "ast_domain.of_type D oT T \<longleftrightarrow>
    set (primitives oT) \<subseteq> ((set (types D))\<inverse>)\<^sup>* `` set (primitives T)"
    using ast_domain.of_type_def by simp
  also have "... \<longleftrightarrow>
    set (primitives oT) \<subseteq> ((set (types D))\<^sup>*)\<inverse> `` set (primitives T)"
    by (simp add: rtrancl_converse)
  also have "... \<longleftrightarrow>
    (\<forall>ot \<in> set (primitives oT). ot \<in> ((set (types D))\<^sup>*)\<inverse> `` set (primitives T))" by auto
  also have "... \<longleftrightarrow>
    (\<forall>ot \<in> set (primitives oT). \<exists>t. (ot, t) \<in> (set (types D))\<^sup>* \<and> t \<in> set (primitives T))" by auto
  finally show ?thesis using reachable_iff_in_star by metis
qed

lemma obj_of_type_iff_reach:
  assumes "ast_problem.objT P n = Some oT"
  shows  "ast_problem.is_obj_of_type P n T \<longleftrightarrow>
    (\<forall>ot \<in> set (primitives oT).
      \<exists>t \<in> set (primitives T).
    t \<in> set (reachable_nodes (types (domain P)) ot))"
  using assms ast_problem.is_obj_of_type_def of_type_iff_reach by auto

lemma single_of_type_iff:
  shows "ast_domain.of_type D (Either [ot]) T \<longleftrightarrow> (
    \<exists>t \<in> set (primitives T).
      t \<in> set (reachable_nodes (types D) ot))"
  using of_type_iff_reach by simp

lemma simple_obj_of_type_iff:
  assumes "ast_problem.objT P n = Some (Either [ot])"
  shows  "ast_problem.is_obj_of_type P n T \<longleftrightarrow>
      (\<exists>t \<in> set (primitives T).
    t \<in> set (reachable_nodes (types (domain P)) ot))"
  using assms ast_problem.is_obj_of_type_def single_of_type_iff by auto

(* type normalization well-formed *)
lemma dist_prefix: "distinct xs \<Longrightarrow> distinct (map ((@) (safe_prefix ys)) xs)"
  by (simp add: distinct_conv_nth)
lemma dist_pred: "distinct xs \<Longrightarrow> distinct (map Pred xs)"
  by (meson distinct_map inj_onI predicate.inject)

lemma t_preds_names: (* TODO simplify *)
  assumes "distinct (map pred (predicates D))"
  shows "distinct (map pred (type_preds D @ detype_preds (predicates D)))"
proof -
  (* Predicate names are unique because the original predicate names are unchanged
     and the additional predicate names are unique (based on unique type names)
     and distinct from the original predicates. *)
  let ?preds = "map pred (predicates D)"
  let ?t_preds = "map pred (type_preds D)"
  let ?dt_preds = "map pred (detype_preds (predicates D))"

  have p_eq_dt: "?preds = ?dt_preds" by simp
  hence g1: "distinct ( map pred (detype_preds (predicates D)))"
    using assms by argo

  let ?prefix = "safe_prefix (map predicate.name ?preds)"
  (* =  map (pred_for_type D) (type_names D) *)
  have dist_types: "distinct (type_names D)" by auto
  have t_ps_expand: "?t_preds = map (Pred \<circ> ((@) ?prefix)) (type_names D)"
    by (simp add: pred_names_def)
  (* define, not let, because the terms become too big for the solver *)
  define pnames where "pnames \<equiv> map predicate.name ?preds"
  define tp_names where "tp_names \<equiv> map (((@) (safe_prefix pnames))) (type_names D)"
  
  have "set (map ((@) (safe_prefix pnames)) (type_names D)) \<inter> set pnames = {}"
    using safe_prefix_correct by auto
  hence "set tp_names \<inter> set pnames = {}" using tp_names_def pnames_def by simp
  hence "set (map Pred tp_names) \<inter> set (map Pred pnames) = {}" by auto
  hence "set (map (Pred \<circ> ((@) (safe_prefix pnames))) (type_names D)) \<inter> set (map Pred pnames) = {}"
    using tp_names_def by (metis map_map)

  moreover have "map Pred pnames = ?preds" using pnames_def by simp
  moreover have "?t_preds = map (Pred \<circ> ((@) (safe_prefix pnames))) (type_names D)"
    using t_ps_expand pnames_def by blast
  ultimately have g2: "set ?t_preds \<inter> set ?dt_preds = {}" by (metis p_eq_dt)
  
  have d: "distinct (map ((@) ?prefix) (type_names D))"
    using dist_prefix dist_types by simp
  hence "distinct (map (Pred \<circ> ((@) ?prefix)) (type_names D))"
    using dist_pred[OF d] by simp
  hence g3: "distinct (?t_preds)" using t_ps_expand by metis

  from g1 g2 g3 show ?thesis by simp
qed

lemma t_preds_names2:
  assumes "distinct (map pred (predicates D))"
  shows "distinct (map pred (predicates (detype_dom D)))"
  using assms
  using t_preds_names ast_domain.sel(2) detype_dom.simps by presburger

lemma t_preds_wf:
  "\<forall>p \<in> set (type_preds D @ (detype_preds (predicates D))).
    ast_domain.wf_predicate_decl (detype_dom D) p"
  (is "\<forall>p \<in> ?s. ?wf p")
proof -
  let ?D2 = "detype_dom D"
  have c1: "\<forall>p \<in> set (type_preds D). ?wf p"
  proof
    fix p assume "p \<in> set (type_preds D)"
    hence "\<forall>t \<in> set (argTs p). ast_domain.wf_type ?D2 t" using wf_object by auto
    thus "?wf p"
      by (metis ast_domain.wf_predicate_decl.simps predicate_decl.exhaust_sel)
  qed
  have c2: "\<forall>p \<in> set (detype_preds (predicates D)). ?wf p"
  proof
    fix p assume "p \<in> set (detype_preds (predicates D))"
    hence "\<forall>t \<in> set (argTs p). t = Either [''object'']" by auto
    hence "\<forall>t \<in> set (argTs p). ast_domain.wf_type ?D2 t" using wf_object by auto
    thus "?wf p"
      by (metis ast_domain.wf_predicate_decl.simps predicate_decl.exhaust_sel)
  qed
  (* just to speed things up *)
  have "\<And>xs ys P. \<forall>x \<in> set xs. P x \<Longrightarrow> \<forall>y \<in> set ys. P y \<Longrightarrow> \<forall>x' \<in> set (xs @ ys). P x'"
    by auto
  note this[OF c1 c2] thus ?thesis .
qed

lemma t_ents_names:
  assumes "distinct (map fst ents)"
  shows "distinct (map fst (detype_ents ents))"
proof -
  have "\<And>xs. map fst xs = map fst (map detype_ent xs)" by auto
  thus ?thesis using assms by (metis detype_ents_def)
qed

(* did I mess up simp somehow? why is this getting harder? *)
lemma t_ents_wf_aux:
  shows "(\<forall>ent\<in>set (detype_ents ents). ast_domain.wf_type (detype_dom D) (snd ent))"
proof
  fix ent assume elem: "ent \<in> set (detype_ents ents)"
  obtain n T where nT: "(n, T) = ent" by (metis surjective_pairing)

  from elem nT obtain og where "og \<in> set ents" and 2: "ent = detype_ent og"
    by (metis (mono_tags, lifting) detype_ents_def image_iff list.set_map)
  from nT 2 have "T = Either [''object'']" by (metis detype_ent.elims prod.inject)
  hence "ast_domain.wf_type (detype_dom D) T" using wf_object by simp
  thus "ast_domain.wf_type (detype_dom D) (snd ent)" using nT by fastforce
qed

lemma t_ents_wf:
  shows "(\<forall>(n,T)\<in>set (detype_ents ents). ast_domain.wf_type (detype_dom D) T)"
  using t_ents_wf_aux by fastforce

(* formulas *)

(* Detyped formulas *)

lemma
  "map (\<lambda>t. y) xs = replicate (length xs) y"
  by (simp add: map_replicate_const)

(* pred sig ts \<Longrightarrow> detype pred sig (detype ts)*)
lemma
  assumes "distinct (map pred (predicates D))"
  assumes "ast_domain.sig D p = Some Ts"
  shows "ast_domain.sig (detype_dom D) p
    = Some (replicate (length Ts) (Either [''object'']))"
proof -
  from assms have "PredDecl p Ts \<in> set (predicates D)" using sig_some by blast
  have "predicates (detype_dom D) =
    map (\<lambda>pd. PredDecl (pred pd) (replicate (length (argTs pd)) (Either [''object'']))) (predicates D)"
  oops




(* ty_term (map_of params) constT *)

(* fun wf_pred_atom_c :: "ast_domain \<Rightarrow> ('ent \<rightharpoonup> type) \<Rightarrow> predicate \<times> 'ent list \<Rightarrow> bool" where
  "wf_pred_atom_c D ty_ent (p,vs) \<longleftrightarrow> (
    case (sig_c D) p of
      None \<Rightarrow> False
    | Some Ts \<Rightarrow> list_all2 (is_of_type_c D ty_ent) vs Ts)" *)

(* I feel like I need to figure out how to make my formulas smaller *)
lemma
  assumes "ast_domain.wf_pred_atom D (ty_term (map_of params) (ast_domain.constT D )) (p,vs)"
  defines "D2 \<equiv> (detype_dom D)"
  shows "ast_domain.wf_pred_atom D2 (ty_term (map_of (detype_ents params)) (ast_domain.constT D2)) (p,vs)"
proof -
  let ?tyt = "ty_term (map_of params) (ast_domain.constT D )"
  let ?tyt2 = "ty_term (map_of (detype_ents params)) (ast_domain.constT D2)"
  
  from assms obtain Ts where "ast_domain.sig D p = Some Ts \<and> list_all2 (ast_domain.is_of_type D ?tyt) vs Ts"
    by (metis not_None_eq option.simps(4-5) ast_domain.wf_pred_atom.simps)
  hence "length vs = length Ts" using list_all2_lengthD by auto



  oops

(* actions *)



lemma t_acs_names:
  assumes "distinct (map ast_action_schema.name (actions D))"
  shows "distinct (map ast_action_schema.name (map (detype_ac D) (actions D)))"
proof -
  have "\<And>ac. ast_action_schema.name ac = ast_action_schema.name (detype_ac D ac)"
    by (metis ast_action_schema.collapse ast_action_schema.sel(1) detype_ac.simps)
  (* I'd like composition syntax but the automatic solver doesn't like me today *)
  hence "map ast_action_schema.name (actions D) = map ast_action_schema.name (map (detype_ac D) (actions D))"
    by simp
  thus ?thesis using assms by argo
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

lemma "\<forall>x \<in> set xs. P x \<Longrightarrow> \<forall>x. P x \<longrightarrow> Q (f x) \<Longrightarrow> \<forall>x \<in> set (map f xs). Q x"
  by simp

lemma wf_ac_expanded: "ast_domain.wf_action_schema D a \<longleftrightarrow> (
      let
        tyt = ty_term (map_of (parameters a)) (ast_domain.constT D)
      in
        distinct (map fst (parameters a))
      \<and> ast_domain.wf_fmla D tyt (ast_action_schema.precondition a)
      \<and> ast_domain.wf_effect D tyt (ast_action_schema.effect a))"
  using ast_domain.wf_action_schema.simps
  by (metis ast_action_schema.collapse)

lemma t_acs_wf_aux:
  assumes "ast_domain.wf_action_schema D a"
  shows "ast_domain.wf_action_schema (detype_dom D) (detype_ac D a)"
proof -
  let ?D2 = "detype_dom D"
  let ?a2 = "detype_ac D a"
  define tyt where tyt: "tyt \<equiv> ty_term (map_of (parameters a)) (ast_domain.constT D)"
  from assms have 1: "distinct (map fst (parameters a))" using wf_ac_expanded by metis
  from assms tyt have 2: "ast_domain.wf_fmla D tyt (ast_action_schema.precondition a)" using wf_ac_expanded by metis
  from assms tyt have 3: "ast_domain.wf_effect D tyt (ast_action_schema.effect a)" using wf_ac_expanded by metis

  define tyt2 where tyt2: "tyt2 \<equiv> ty_term (map_of (parameters ?a2)) (ast_domain.constT ?D2)"
  have ps: "parameters ?a2 = detype_ents (parameters a)"
    by (metis ast_action_schema.collapse ast_action_schema.sel(2) detype_ac.simps)
  hence c1: "distinct (map fst (parameters ?a2))" using 1 t_ents_names by auto
  from ps have cx: "(\<forall>(n,T)\<in>set (parameters ?a2). ast_domain.wf_type (detype_dom D) T)"
    using t_ents_wf by metis (* not required for wf_action_schema but should be, maybe *)

  have c2a: "ast_domain.wf_fmla ?D2 tyt2 (param_precond D (parameters a))" sorry
  have c2b: "ast_domain.wf_fmla ?D2 tyt2 (ast_action_schema.precondition a)" sorry
  from c2a c2b have c2: "ast_domain.wf_fmla ?D2 tyt2 (ast_action_schema.precondition ?a2)"
    by (metis ast_action_schema.collapse ast_action_schema.sel(3) ast_domain.wf_fmla.simps(3) detype_ac.simps)
  have "ast_domain.wf_effect ?D2 tyt2 (ast_action_schema.effect a)" sorry
  hence c3: "ast_domain.wf_effect ?D2 tyt2 (ast_action_schema.effect ?a2)"
    by (metis ast_action_schema.collapse ast_action_schema.sel(4) detype_ac.simps)

  from c1 c2 c3 tyt2 show ?thesis using wf_ac_expanded by auto
qed

lemma t_acs_wf:
  assumes "\<forall>a\<in>set (actions D). ast_domain.wf_action_schema D a"
  shows "(\<forall>a\<in>set (map (detype_ac D) (actions D)). ast_domain.wf_action_schema (detype_dom D) a)"
  oops
  

theorem detype_dom_wf:
  assumes "ast_domain.wf_domain D"
  shows "ast_domain.wf_domain (detype_dom D)"
proof -
  let ?D2 = "detype_dom D"
  from assms have
    typs: "ast_domain.wf_types D" and
    pred_names: "distinct (map pred (predicates D))" and
    wf_preds: "\<forall>p\<in>set (predicates D). ast_domain.wf_predicate_decl D p" and
    cnst_names: "distinct (map fst (consts D))" and
    wf_cnsts: "\<forall>(n,T)\<in>set (consts D). ast_domain.wf_type D T" and
    ac_names: "distinct (map ast_action_schema.name (actions D))" and
    wf_acs: "\<forall>a\<in>set (actions D). ast_domain.wf_action_schema D a"
    by (simp_all add: ast_domain.wf_domain_def)

  (* Types are well-formed because they are simply empty. *)
  have c1: "ast_domain.wf_types ?D2" using ast_domain.wf_types_def by simp
  note c2 = t_preds_names[OF pred_names]
  note c3 = t_preds_wf
  have c4: "distinct (map fst (detype_ents(consts D)))"
    using cnst_names by (simp add: t_ents_names)
  have c5: "(\<forall>(n,T)\<in>set (detype_ents (consts D)). ast_domain.wf_type ?D2 T)"
    using wf_cnsts t_ents_wf by metis
  have c6: "distinct (map ast_action_schema.name (map (detype_ac D) (actions D)))"
    using ac_names t_acs_names by simp
  have c7: "(\<forall>a\<in>set (map (detype_ac D) (actions D)). ast_domain.wf_action_schema ?D2 a)" sorry

  from c1 c2 c3 c4 c5 c6 c7 show ?thesis
    using ast_domain.wf_domain_def by auto
qed

lemma "distinct nams \<Longrightarrow> distinct (map Pred nams)"
  by (meson distinct_map inj_onI predicate.inject)


lemma "set as \<inter> set bs = {} \<Longrightarrow> distinct as \<Longrightarrow> distinct bs \<Longrightarrow> distinct (as @ bs)"
  by simp


lemma "ast_problem.wf_problem P \<Longrightarrow> ast_problem.wf_problem (detype_prob P)"
  oops

lemma "ast_domain.wf_domain D \<Longrightarrow> typeless_dom (detype_dom D)"
  oops

lemma "ast_problem.wf_problem P \<Longrightarrow> typeless_prob (detype_prob P)"
  oops

(* type normalization correct w.r.t. execution*)

lemma "ast_problem.valid_plan P \<pi> \<Longrightarrow> ast_problem.valid_plan (detype_prob P) \<pi>"
  oops


end