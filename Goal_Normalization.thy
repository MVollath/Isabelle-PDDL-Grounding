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

lemma g_objT:
  "objT = p3.objT"
  using g_constT d3.constT_def p3.objT_def degoal_prob_sel by simp

lemma g_eff_wf:
  assumes "wf_effect tyt \<epsilon>" shows "d3.wf_effect tyt \<epsilon>"
  using assms apply (cases \<epsilon>; simp)
  using ast_domain.wf_fmla_atom_alt g_fmla_wf by blast

lemma g_wm_wf:
  assumes "wf_world_model wm" shows "p3.wf_world_model wm"
  using assms ast_problem.wf_world_model_def ast_domain.wf_fmla_atom_alt
    degoal_prob_sel(1) g_fmla_wf g_objT by metis

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
  shows "wf_fmla (ty_term xd tyt) (map_atom_fmla term.CONST F)"
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

lemma degoal_prob_wf: "p3.wf_problem"
proof -
  note degoal_prob_sel[simp] degoal_dom_sel[simp]
  note c1 = degoal_dom_wf
  have c2: "distinct (map fst (objects degoal_prob) @ map fst (consts p3.D))"
    using wf_D wf_P by simp
  have c3: "\<forall>(n, y) \<in> set (objects degoal_prob). p3.wf_type y" by simp (* empty list *)
  note c4 = wf_P(3)
  have c5: "p3.wf_world_model (set (init P))" using g_wm_wf wf_P(4) by simp
  have c6: "p3.wf_fmla p3.objT (goal degoal_prob)"
    (* d_preds_dist not needed, since goal_pred is the first in the list *)
    using d3.sig_def goal_pred_decl_def by auto
  from c1 c2 c3 c4 c5 c6 show ?thesis using p3.wf_problem_def by simp
qed

end

sublocale wf_ast_problem3 \<subseteq> d3: wf_ast_domain D3
  using degoal_dom_wf wf_ast_domain.intro by simp

sublocale wf_ast_problem3 \<subseteq> p3: wf_ast_problem P3
  using degoal_prob_wf wf_ast_problem.intro by simp

context wf_ast_problem3 begin

abbreviation "\<pi>\<^sub>g \<equiv> PAction goal_ac_name []"

lemma resolve_ac_g:
  "p3.resolve_action_schema goal_ac_name = Some (goal_ac term_goal)"
  using goal_ac_def p3.res_aux degoal_prob_sel degoal_dom_sel by simp

lemma wf_pa_g:
  "p3.wf_plan_action \<pi>\<^sub>g"
proof -
  have "p3.action_params_match (goal_ac term_goal) []"
    unfolding goal_ac_def p3.action_params_match_def by simp
  with resolve_ac_g show ?thesis using p3.wf_plan_action_simple by fastforce
qed

term "(map_formula\<circ>map_atom) term.CONST (\<phi>::object atom formula)"

lemma term_to_obj: "ac_tsubst [] [] (term.CONST x) = x"
  unfolding ac_tsubst_def by simp

(* this is more involved than I thought... *)
lemma term_to_obj_atom:
  shows "map_atom (ac_tsubst [] []) (map_atom term.CONST x) = x"
proof (cases x)
  case (predAtm p xs)
  hence "map_atom (ac_tsubst [] []) (map_atom term.CONST x)
    = predAtm p (map (ac_tsubst [] [] \<circ> term.CONST) xs)"
    by simp
  also have "... = predAtm p xs" using term_to_obj
    by (simp add: map_idI)
  finally show ?thesis using predAtm by simp
qed (simp add: term_to_obj)

lemma term_to_obj_fmla:
  shows "map_atom_fmla (ac_tsubst [] []) (map_atom_fmla term.CONST F) = F"
  by (induction F; simp add: term_to_obj_atom)

lemma resinst_ac_g:
  "p3.resolve_instantiate \<pi>\<^sub>g = Ground_Action (goal P) goal_effect"
proof -
  have "goal_ac term_goal \<in> set (actions D3)" using degoal_dom_sel by simp
  hence "p3.resolve_instantiate \<pi>\<^sub>g = Ground_Action
    (map_atom_fmla (ac_tsubst [] []) term_goal)
    (map_ast_effect (ac_tsubst [] []) goal_effect)"
    using goal_ac_def p3.resolve_instantiate_cond
    by (simp add: degoal_prob_sel(1))
  moreover have "(map_ast_effect (ac_tsubst [] []) goal_effect) = goal_effect" by simp
    (* Very simple because there are no parameters, so nothing is actually being mapped.
       Only the type of an empty list is changed. *)
  moreover have "map_atom_fmla (ac_tsubst [] []) term_goal = goal P"
    using term_to_obj_fmla by (simp add: term_goal_def)
  ultimately show ?thesis by simp
qed

thm wf_execute   
lemma "wf_world_model M \<Longrightarrow> wm_basic M"
  by (meson g_wm_wf p3.wf_fmla_atom_alt p3.wf_world_model_def wm_basic_def)

lemma goal_sem:
  assumes "wf_world_model M" "M \<^sup>c\<TTurnstile>\<^sub>= goal P"
  shows
    "p3.plan_action_enabled \<pi>\<^sub>g M"
    "p3.execute_plan_action \<pi>\<^sub>g M \<^sup>c\<TTurnstile>\<^sub>= goal P3"
proof -
  from assms resinst_ac_g wf_pa_g show "p3.plan_action_enabled \<pi>\<^sub>g M"
    using p3.plan_action_enabled_def by simp

  from assms(1) this
  have basic: "wm_basic (p3.execute_plan_action \<pi>\<^sub>g M)"
    using g_wm_wf p3.wf_execute p3.wf_fmla_atom_alt p3.wf_world_model_def wm_basic_def
    by metis

  from resinst_ac_g have "effect (p3.resolve_instantiate \<pi>\<^sub>g) = goal_effect"
    by simp
  hence "Atom (predAtm goal_pred []) \<in> p3.execute_plan_action \<pi>\<^sub>g M"
    using p3.execute_plan_action_def by simp
  hence "valuation (p3.execute_plan_action \<pi>\<^sub>g M) \<Turnstile> goal P3" using degoal_prob_sel(4)
    using valuation_def by simp
  with basic show "p3.execute_plan_action \<pi>\<^sub>g M \<^sup>c\<TTurnstile>\<^sub>= goal P3"
    using valuation_iff_close_world by simp
qed

lemma g_obj_of_type:
  "is_obj_of_type = p3.is_obj_of_type"
  unfolding ast_problem.is_obj_of_type_alt ast_domain.is_of_type_def ast_domain.of_type_def
    ast_domain.subtype_rel_def
  using g_objT degoal_dom_sel(1) degoal_prob_sel(1) by metis

(* TODO clean up *)
lemma g_pa_wf_right:
  assumes "wf_plan_action \<pi>"
  shows 
    "resolve_instantiate \<pi> = p3.resolve_instantiate \<pi> \<and> p3.wf_plan_action \<pi>"
using assms proof (cases \<pi>)
  case (PAction n args)
  with assms obtain ac where 1:
    "resolve_action_schema n = Some ac" "ac \<in> set (actions D)" "ac_name ac = n"
    by (meson wf_pa_refs_ac)
  hence "ac \<in> set (actions D3)" using degoal_dom_sel by simp
  with 1 have r: "d3.resolve_action_schema n = Some ac"
    using degoal_prob_sel by (metis p3.res_aux)
  hence g1: "resolve_instantiate \<pi> = p3.resolve_instantiate \<pi>"
    using degoal_prob_sel 1 PAction by simp

  from 1 assms have "action_params_match ac args" by (simp add: PAction)
  hence "p3.action_params_match ac args"
    unfolding ast_problem.action_params_match_def
    using g_obj_of_type by simp
  with r have g2: "p3.wf_plan_action \<pi>" using p3.wf_plan_action_simple PAction
    using degoal_prob_sel(1) PAction by fastforce

  from g1 g2 show ?thesis by simp
qed


lemma g_exec_right:
  assumes "wf_plan_action \<pi>"
  shows "execute_plan_action \<pi> M = p3.execute_plan_action \<pi> M"
  using assms ast_problem.execute_plan_action_def g_pa_wf_right by simp

lemma g_enab_right:
  assumes "wf_plan_action \<pi>"
  shows "plan_action_enabled \<pi> M = p3.plan_action_enabled \<pi> M"
  using assms g_pa_wf_right ast_problem.plan_action_enabled_def by simp

lemma g_execs_right:
  assumes "wf_world_model M" "plan_action_path M \<pi>s M'"
  shows "p3.plan_action_path M \<pi>s M'"
  using assms proof (induction \<pi>s arbitrary: M)
case (Cons p ps)
  hence 0: "plan_action_enabled p M \<and> plan_action_path (execute_plan_action p M) ps M'"
    using plan_action_path_Cons by simp
  with Cons have 1: "p3.plan_action_enabled p M" using g_enab_right
    by (simp add: plan_action_path_def)
  from wf_execute 0
  have "wf_world_model (execute_plan_action p M)"
    by (simp add: Cons.prems(1))
  note Cons.IH[OF this]
  with 0 have "p3.plan_action_path (execute_plan_action p M) ps M'" by simp
  then show ?case
    using "1" Cons.prems(2) g_exec_right plan_action_path_def by force
qed simp

thm plan_action_path_Cons

lemma (in wf_ast_problem) valid_plan_from_Cons[simp]:
  "valid_plan_from M (\<pi> # \<pi>s)
    \<longleftrightarrow> valid_plan_from (execute_plan_action \<pi> M) \<pi>s \<and> plan_action_enabled \<pi> M"
  using valid_plan_from_def by auto

lemma (in wf_ast_problem) valid_plan_from_append:
  "valid_plan_from M (\<pi>s @ [\<pi>])
    \<longleftrightarrow> (\<exists>M'. plan_action_path M \<pi>s M' \<and> plan_action_enabled \<pi> M' \<and>
    execute_plan_action \<pi> M' \<^sup>c\<TTurnstile>\<^sub>= goal P)"
  using valid_plan_from_def by (induction \<pi>s arbitrary: M; simp)


lemma valid_plan_right:
  assumes "valid_plan \<pi>s"
  shows "p3.valid_plan (\<pi>s @ [\<pi>\<^sub>g])"
proof -

  from assms obtain M where 1: "plan_action_path I \<pi>s M" and 2: "M \<^sup>c\<TTurnstile>\<^sub>= goal P"
    using valid_plan_def valid_plan_from_def by auto
  
  from 1 have wf_m: "wf_world_model M"
    using wf_I wf_plan_action_path by blast
  from 1 have "p3.plan_action_path p3.I \<pi>s M"
    using ast_problem.I_def g_execs_right degoal_prob_sel(3) wf_I by auto
  moreover from 2 wf_m have "p3.plan_action_enabled \<pi>\<^sub>g M"
           "p3.execute_plan_action \<pi>\<^sub>g M \<^sup>c\<TTurnstile>\<^sub>= goal P3"
    using goal_sem by simp_all
  ultimately show ?thesis
    using p3.valid_plan_from_append
    using p3.valid_plan_def by auto
qed

end


end