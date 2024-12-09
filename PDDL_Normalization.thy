theory PDDL_Normalization
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

definition detype_ents :: "('ent \<times> type) list \<Rightarrow> ('ent \<times> type) list" where
  "detype_ents params \<equiv> map (\<lambda>(v, t). (v, Either [''object''])) params"

fun detype_ac :: "ast_domain \<Rightarrow> ast_action_schema \<Rightarrow> ast_action_schema" where
  "detype_ac D (Action_Schema nam params pre eff) =
    Action_Schema nam (detype_ents params) (param_precond D params \<^bold>\<and> pre) eff"

fun detype_preds :: "predicate_decl list \<Rightarrow> predicate_decl list" where
  "detype_preds preds =
    map (\<lambda>pd. PredDecl (pred pd) (map (\<lambda>t. Either [''object'']) (argTs pd))) preds"

fun detype_dom :: "ast_domain \<Rightarrow> ast_domain" where
  "detype_dom D = (case D of (Domain typs preds objs acs) \<Rightarrow>
    Domain
      []
      (type_preds D @ detype_preds preds)
      (detype_ents objs)
      (map (detype_ac D) acs))"

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

(* Ziel für 12.12. *)
theorem "ast_domain.wf_domain D \<Longrightarrow> ast_domain.wf_domain (detype_dom D)"
  oops

lemma "ast_problem.wf_problem P \<Longrightarrow> ast_problem.wf_problem (detype_prob P)"
  oops

lemma "ast_domain.wf_domain D \<Longrightarrow> typeless_dom (detype_dom D)"
  oops

lemma "ast_problem.wf_problem P \<Longrightarrow> typeless_prob (detype_prob P)"
  oops

(* type normalization correct w.r.t. execution*)

lemma "ast_problem.valid_plan P \<pi> \<Longrightarrow> ast_problem.valid_plan (detype_prob P) \<pi>"
  oops


section \<open> Context setup that I'm totally gonna use eventually \<close>

(*context wf_ast_problem
begin
definition "goal_only_conj \<equiv> only_conj (goal P)"

definition "typeless_pddl \<equiv> P \<noteq> P" (* just to force P into signature *)
definition "normalized_pddl \<equiv> typeless_pddl \<and> False"
end

lemma
  assumes
    "ast_problem.wf_problem P"
    "ast_domain.resolve_action_schema (domain P) (name \<pi>) = Some a"
    "ast_problem.action_params_match P a params"
    "M \<^sup>c\<TTurnstile>\<^sub>= precondition (ast_problem.resolve_instantiate P \<pi>)"
  shows "True" oops

(* can't move this into a context, can I? *)
fun normalize_pddl :: "ast_problem \<Rightarrow> ast_problem" where
  "normalize_pddl P =
    (let typs = types (domain P) in undefined)"

locale restr_ast_problem = wf_ast_problem P for P +
  assumes input_restrictions: goal_only_conj
  (* The STRIPS output doesn't allow disjunctions in goals. Helmert doesn't have this problem,
  because his output is SASP, where axioms can be used to circumvent this issue.
  TODO: just solve this by introducing auxiliary actions. *)
begin
lemma types_away_typeless:
  shows "wf_ast_problem.typeless_pddl (types_away P)"
  oops

lemma norm_normal: "wf_ast_problem.normalized_pddl (normalize_pddl P)" oops
(* probably need to prove this similar to ElGroundo: have normalization output a
  bijection for ground actions and for ground predicates. *)
lemma norm_sol:
  assumes "P' = normalize_pddl P"
  shows "\<exists>\<pi>. valid_plan \<pi> \<longleftrightarrow> (\<exists>\<pi>'. ast_problem.valid_plan P' \<pi>')"
  oops

(* If I want to be really funny, I can perform normalization without splitting the actions,
  we can just re-use the old plan actions *)
theorem norm_sol_funny:
  assumes "P' = normalize_pddl P"
  shows "valid_plan \<pi> \<longleftrightarrow> ast_problem.valid_plan P' \<pi>"
  oops
end

locale normalized_ast_problem = wf_ast_problem P for P +
  assumes normalized: "normalized_pddl"
begin

end *)



end