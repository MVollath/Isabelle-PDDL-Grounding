theory Goal_Normalization
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    Type_Normalization Utils AbLa_alts DNF
begin

context ast_domain begin

  definition "goal_pred \<equiv> Pred (make_unique pred_names ''Goal'')"
  definition "goal_pred_decl \<equiv> PredDecl goal_pred []"
  
  abbreviation "ac_names \<equiv> map ac_name (actions D)"
  
  abbreviation "goal_ac_name \<equiv> make_unique ac_names ''Goal''"
  
  abbreviation "goal_effect \<equiv> Effect [Atom (predAtm goal_pred [])] []"
  
  definition goal_ac where "goal_ac g =
    Action_Schema goal_ac_name [] g goal_effect"
end

definition "obj_to_term obj \<equiv> term.VAR obj"

context ast_problem begin

  definition "term_goal \<equiv> (map_formula\<circ>map_atom) term.CONST (goal P)"
  
  definition "degoal_dom \<equiv>
    Domain
      (types D)
      (goal_pred_decl # predicates D)
      (objects P @ consts D)
      (goal_ac term_goal # actions D)"
  
  definition "degoal_prob \<equiv>
    Problem
      degoal_dom
      []
      (init P)
      (Atom (predAtm goal_pred []))"

end

abbreviation (in ast_problem) (input) "D3 \<equiv> degoal_dom"
abbreviation (in ast_problem) (input) "P3 \<equiv> degoal_prob"

locale ast_problem3 = ast_problem
sublocale ast_problem3 \<subseteq> d3: ast_domain D3 .
sublocale ast_problem3 \<subseteq> p3: ast_problem P3 .

locale wf_ast_problem3 = wf_ast_problem
sublocale wf_ast_problem3 \<subseteq> d3: ast_domain D3 .
sublocale wf_ast_problem3 \<subseteq> p3: ast_problem P3 .

subsection \<open> Alternate/simplified definitions\<close>
context ast_problem begin

lemma degoal_dom_sel:
  "types D3 = types D"
  "predicates D3 = goal_pred_decl # predicates D"
  "consts D3 = objects P @ consts D"
  "actions D3 = goal_ac term_goal # actions D"
  using degoal_dom_def by simp_all

lemma degoal_prob_sel:
  "domain P3 = degoal_dom"
  "objects P3 = []"
  "init P3 = init P"
  "goal P3 = Atom (predAtm goal_pred [])"
  using degoal_prob_def by simp_all
end

subsection \<open>Well-Formedness\<close>

context wf_ast_problem3 begin


lemma pred_stack: "Pred ` predicate.name ` ps = ps" by force

lemma g_preds_dist: "distinct (map pred (predicates D3))"
proof -
  have "make_unique pred_names ''Goal'' \<notin> set pred_names"
    using made_unique by blast
  hence "make_unique pred_names ''Goal'' \<notin> predicate.name ` (pred ` set (predicates D))"
    by auto
  hence "goal_pred \<notin> pred ` set (predicates D)"
    unfolding goal_pred_def using pred_stack by blast
  hence "pred goal_pred_decl \<notin> pred ` set (predicates D)"
    using goal_pred_decl_def by force
  thus ?thesis
    using wf_D(2) degoal_dom_sel(2) by auto
qed

lemma g_type_wf: "wf_type T \<Longrightarrow> d3.wf_type T"
  using degoal_dom_sel(1) by (cases T) simp

lemma g_preds_wf: "list_all1 d3.wf_predicate_decl (predicates D3)"
proof -
  have "wf_predicate_decl pd \<Longrightarrow> d3.wf_predicate_decl pd" for pd
    using g_type_wf by (cases pd) simp

  hence "list_all1 d3.wf_predicate_decl (predicates D)"
    using wf_D(3) degoal_dom_sel(2) by simp
  moreover have "d3.wf_predicate_decl goal_pred_decl"
    unfolding goal_pred_decl_def by simp

  ultimately show ?thesis using degoal_dom_sel(2) by simp
qed

lemma g_acs_dist: "distinct (map ac_name (actions D3))"
proof -
  have "goal_ac_name \<notin> set ac_names"
    using made_unique by blast
  hence "ac_name (goal_ac term_goal) \<notin> ac_name ` set (actions D)"
    using ast_domain.goal_ac_def by fastforce
  thus ?thesis using degoal_dom_sel wf_D(6) by auto
qed

thm wf_action_schema.simps
thm wf_action_schema_alt

lemma g_sig:
  assumes "sig p = Some xs" shows "d3.sig p = Some xs"
proof -
  from assms have "PredDecl p xs \<in> set (predicates D3)"
    using sig_Some degoal_dom_sel by simp
  thus ?thesis using pred_resolve g_preds_dist degoal_dom_sel d3.sig_def by metis
qed

lemma g_fmla_wf:
  assumes "wf_fmla tyt \<phi>" shows "d3.wf_fmla tyt \<phi>"
  using assms
proof (induction \<phi>)
  case (Atom x) thus ?case
  proof (cases x)
    case (predAtm p xs)
    hence a: "wf_pred_atom tyt (p, xs)" using assms Atom by simp
    then obtain Ts where sig: "sig p = Some Ts"
      by fastforce
    with a have "list_all2 (is_of_type tyt) xs Ts" by simp
    hence "list_all2 (d3.is_of_type tyt) xs Ts"
      unfolding ast_domain.is_of_type_def ast_domain.of_type_def ast_domain.subtype_rel_def degoal_dom_sel(1)
      by simp
    moreover have "d3.sig p = Some Ts" using g_sig sig by simp
    ultimately have "d3.wf_pred_atom tyt (p, xs)" by simp
    then show ?thesis using predAtm by simp
  qed simp
qed auto

lemma g_constT:
  "objT = d3.constT"
  using objT_def degoal_dom_sel d3.constT_def
  using constT_def map_le_iff_map_add_commute objm_le_objT by auto

lemma g_eff_wf:
  assumes "wf_effect tyt \<epsilon>" shows "d3.wf_effect tyt \<epsilon>"
  using assms apply (cases \<epsilon>; simp)
  using ast_domain.wf_fmla_atom_alt g_fmla_wf by blast

lemma wf_fmla_mono:
  assumes "tys \<subseteq>\<^sub>m tys'" "wf_fmla tys \<phi>"
  shows "wf_fmla tys' \<phi>"
  using assms apply (induction \<phi>)
  apply (simp add: wf_atom_mono) by simp_all

lemma wf_eff_mono:
  assumes "tys \<subseteq>\<^sub>m tys'" "wf_effect tys eff"
  shows "wf_effect tys' eff"
  using assms apply (cases eff)
  using wf_fmla_atom_mono by auto

lemma wf_atom_to_term:
  assumes "wf_atom tyt a"
  shows "wf_atom (ty_term xd tyt) (map_atom term.CONST a)"
proof (cases a)
  case (predAtm p xs)
  with assms obtain Ts where sig: "sig p = Some Ts" by fastforce
  from sig have match: "list_all2 (is_of_type tyt) xs Ts" using predAtm assms by simp

  have "list_all2 (is_of_type (ty_term xd tyt)) (map term.CONST xs) Ts"
    using match
  proof (induction xs arbitrary: Ts)
    case (Cons g gs)
    then obtain t ts where ts: "t # ts = Ts"
      by (metis list_all2_Cons1)
    with Cons have 1: "is_of_type tyt g t" "list_all2 (is_of_type tyt) gs ts"
      by auto
    hence "list_all2 (is_of_type (ty_term xd tyt)) (map term.CONST gs) ts"
      "is_of_type (ty_term xd tyt) (term.CONST g) t"
      using Cons.IH apply simp
      using 1 by (simp add: ast_domain.is_of_type_def)
    thus ?case using ts list_all2_Cons1 by auto
  qed simp

  thus ?thesis using predAtm sig by simp
next
  case Eq thus ?thesis using assms by auto
qed

lemma wf_fmla_to_term:
  assumes "wf_fmla tyt F"
  shows "wf_fmla (ty_term xd tyt) ((map_formula \<circ> map_atom) term.CONST F)"
  using assms by (induction F) (simp_all add: wf_atom_to_term)

lemma g_acs_wf: "(\<forall>a\<in>set (actions D3). d3.wf_action_schema a)"
proof -
  have 1: "d3.wf_action_schema ac" if "wf_action_schema ac" for ac
  proof (cases ac)
    case (Action_Schema n params pre eff)

    let ?tyt = "ty_term (map_of params) constT"
    let ?tyt3 = "ty_term (map_of params) d3.constT"
    have tyts: "?tyt \<subseteq>\<^sub>m ?tyt3"
      using degoal_dom_sel ast_domain.constT_def g_constT constT_ss_objT
      by (simp add: ty_term_mono)

    from that have "wf_fmla ?tyt pre \<and> wf_effect ?tyt eff"
      by (metis Action_Schema ast_domain.wf_action_schema.simps)
    hence "d3.wf_fmla ?tyt3 pre \<and> d3.wf_effect ?tyt3 eff" using tyts wf_fmla_mono wf_eff_mono
      using g_eff_wf g_fmla_wf by blast
    moreover have "distinct (map fst params)" using Action_Schema that by (meson wf_action_schema.simps)    
    ultimately show ?thesis using Action_Schema ast_domain.wf_action_schema.simps by simp
  qed

  let ?gac = "goal_ac term_goal"
  have "d3.wf_action_schema ?gac"
  proof -
    have 1: "distinct (map fst (ac_params ?gac))"
      unfolding goal_ac_def by (cases ?gac) simp
    let ?tyt = "ty_term Map.empty d3.constT"
    have 2: "d3.wf_fmla ?tyt term_goal"
      unfolding term_goal_def
      using wf_P g_constT wf_fmla_to_term g_fmla_wf by metis
    have 3: "d3.wf_effect ?tyt goal_effect"
      (* d_preds_dist not needed, since goal_pred is the first in the list *)
      using degoal_dom_sel(2) d3.sig_def goal_pred_decl_def by force
    from 1 2 3 show ?thesis
      by (simp add: goal_ac_def)

  qed
  with 1 show ?thesis using wf_D(7) degoal_dom_sel by simp
qed

lemma degoal_dom_wf: "d3.wf_domain"
proof -
  note degoal_dom_sel[simp]
  have c1: "d3.wf_types" using ast_domain.wf_types_def wf_D by simp
  note c2 = g_preds_dist
  note c3 = g_preds_wf
  have c4: "distinct (map fst (consts D3))" using wf_D wf_P by simp
  have c5: "\<forall>(n, T) \<in> set (consts D3). d3.wf_type T" using wf_D wf_P g_type_wf by auto
  note c6 = g_acs_dist
  note c7 = g_acs_wf
  from c1 c2 c3 c4 c5 c6 c7 show ?thesis using d3.wf_domain_def by simp
qed

end


sublocale restr_domain2 \<subseteq> d2: wf_ast_domain D2
  using detype_dom_wf wf_ast_domain.intro by simp

end