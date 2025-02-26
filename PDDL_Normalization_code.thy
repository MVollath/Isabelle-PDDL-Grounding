theory PDDL_Normalization_code
  imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    Graph_Funs String_Shenanigans DNF
begin
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

subsection \<open>Goal Normalization\<close>

definition goal_pred :: "ast_domain \<Rightarrow> predicate" where
  "goal_pred D \<equiv> Pred (make_unique (pred_names D) ''Goal'')"
definition "goal_pred_decl D \<equiv> PredDecl (goal_pred D) []"
abbreviation "ac_names D \<equiv> map ast_action_schema.name (actions D)"
abbreviation "goal_ac_name D \<equiv> make_unique (ac_names D) ''Goal''"
abbreviation "goal_effect D \<equiv> Effect [Atom (predAtm (goal_pred D) [])] []"

definition goal_ac :: "ast_domain \<Rightarrow> term atom formula \<Rightarrow> ast_action_schema" where
  "goal_ac D g \<equiv> Action_Schema (goal_ac_name D) [] g (goal_effect D)"

definition "term_goal P \<equiv> (map_formula\<circ>map_atom) term.CONST (goal P)"
definition "degoal_dom P \<equiv>
    let D = domain P in
    Domain
      (types D)
      ((goal_pred_decl D) # predicates D)
      (objects P @ consts D)
      (goal_ac D (term_goal P) # actions D)"
  
definition "degoal_prob P \<equiv>
    let D = domain P in
    Problem
      (degoal_dom P)
      []
      (init P)
      (Atom (predAtm (goal_pred D) []))"

abbreviation "\<pi>\<^sub>g P \<equiv> PAction (goal_ac_name (domain P)) []"

subsection "Precondition Normalization"

(*
This part helps ensure that names of the split actions are unique.
This part calculates the DNF for every precondition, only to then discard them again,
before they are later recalculated... This should probably be cached. *)
definition "n_clauses ac \<equiv> length (dnf_list (ast_action_schema.precondition ac))"
definition "max_n_clauses D \<equiv> Max (set (map n_clauses (actions D)))"
definition "prefix_padding D \<equiv> max_length (distinct_strings (max_n_clauses D)) + 1"

(* note that this isn't completely correct yet; if actions are named "A" and "A_", the results aren't unique *)
fun set_n_pre :: " ast_action_schema \<Rightarrow> string \<Rightarrow> term atom formula \<Rightarrow> ast_action_schema" where
  "set_n_pre (Action_Schema _ params _ eff) n pre
  = Action_Schema n params pre eff"


definition "split_ac_names D ac n \<equiv>
  map (\<lambda>prefix. pad (prefix_padding D) prefix @ ast_action_schema.name ac) (distinct_strings n)"


fun split_ac :: "ast_domain \<Rightarrow> ast_action_schema \<Rightarrow> ast_action_schema list" where
  "split_ac D ac =
    (let clauses = dnf_list (ast_action_schema.precondition ac) in
    map2 (set_n_pre ac) (split_ac_names D ac (length clauses)) clauses)"

definition "split_acs D \<equiv> concat (map (split_ac D) (actions D))"

definition "split_dom D \<equiv>
  Domain
    (types D)
    (predicates D)
    (consts D)
    (split_acs D)"

definition "split_prob P \<equiv>
  Problem
    (split_dom (domain P))
    (objects P)
    (init P)
    (goal P)"


(* it's important to be able to convert a plan for the output problem into a plan for the input problem.
  The other direction is probably (hopefully?) not important. *)

fun original_plan_ac where
  "original_plan_ac D (PAction n args) = PAction (drop (prefix_padding D) n) args"

subsection \<open> Relaxation \<close>

fun remove_neg_lits :: "'a formula \<Rightarrow> 'a formula" where
  "remove_neg_lits (Atom a) = Atom a" |
  "remove_neg_lits (\<^bold>\<not>\<bottom>) = (\<^bold>\<not>\<bottom>)" |
  "remove_neg_lits (Atom a \<^bold>\<and> c) = (Atom a \<^bold>\<and> remove_neg_lits c)" |
  "remove_neg_lits (\<^bold>\<not>(Atom a) \<^bold>\<and> c) = remove_neg_lits c"

fun relax_eff :: "'a ast_effect \<Rightarrow> 'a ast_effect" where
  "relax_eff (Effect a b) = Effect a []"

fun relax_ac :: "ast_action_schema \<Rightarrow> ast_action_schema" where
  "relax_ac (Action_Schema n params pre eff) =
    Action_Schema n params (remove_neg_lits pre) (relax_eff eff)"

definition "relax_dom D \<equiv>
  Domain
    (types D)
    (predicates D)
    (consts D)
    (map relax_ac (actions D))"

definition "relax_prob P \<equiv>
  Problem
    (relax_dom (domain P))
    (objects P)
    (init P)
    (remove_neg_lits (goal P))"

end