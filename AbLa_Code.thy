theory AbLa_Code
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
begin

(* suffix _c for "code" *)


subsection \<open> Formulas \<close>

abbreviation cw_entailment_c (infix "\<^sup>c\<TTurnstile>\<^sub>\<equiv>" 53) where
    "M \<^sup>c\<TTurnstile>\<^sub>\<equiv> \<phi> \<equiv> valuation M \<Turnstile> \<phi>"

subsection \<open> Well-Formedness \<close>

text \<open>A hacky way to make the functions in PDDL_STRIPS_Semantics executable.\<close>

definition "subtype_rel_c D \<equiv> set (map prod.swap (types D))"

(* rtrancl has no code for infinite types (such as string) because of the inclusion of Id
  (which only works for enums) so I rewrote this to only use trancl *)
definition of_type_c :: "ast_domain \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" where
  "of_type_c D oT T \<equiv> set (primitives oT) \<subseteq> (subtype_rel_c D)\<^sup>+ `` set (primitives T) \<union> set (primitives T)"
  (* "of_type_c D oT T \<equiv> set (primitives oT) \<subseteq> (subtype_rel_c D)\<^sup>* `` set (primitives T)" *)

definition is_of_type_c :: "ast_domain \<Rightarrow> ('ent \<rightharpoonup> type) \<Rightarrow> 'ent \<Rightarrow> type \<Rightarrow> bool" where
  "is_of_type_c D ty_ent v T \<longleftrightarrow> (
    case ty_ent v of
      Some vT \<Rightarrow> of_type_c D vT T
    | None \<Rightarrow> False)"

definition sig_c :: "ast_domain \<Rightarrow> predicate \<rightharpoonup> type list" where
    "sig_c D \<equiv> map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates D))"

fun wf_pred_atom_c :: "ast_domain \<Rightarrow> ('ent \<rightharpoonup> type) \<Rightarrow> predicate \<times> 'ent list \<Rightarrow> bool" where
  "wf_pred_atom_c D ty_ent (p,vs) \<longleftrightarrow> (
    case (sig_c D) p of
      None \<Rightarrow> False
    | Some Ts \<Rightarrow> list_all2 (is_of_type_c D ty_ent) vs Ts)" (* list_all2 ensures length vs = length Ts *)

text \<open>Predicate-atoms are well-formed if their arguments match the
  signature, equalities are well-formed if the arguments are valid
  objects (have a type).

  TODO: We could check that types may actually overlap
\<close>
fun wf_atom_c :: "ast_domain \<Rightarrow> ('ent \<rightharpoonup> type) \<Rightarrow> 'ent atom \<Rightarrow> bool" where
  "wf_atom_c D ty_ent (predAtm p vs) \<longleftrightarrow> wf_pred_atom_c D ty_ent (p,vs)"
| "wf_atom_c D ty_ent (Eq a b) \<longleftrightarrow> ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None"

text \<open>A formula is well-formed if it consists of valid atoms,
  and does not contain negations, except for the encoding \<open>\<^bold>\<not>\<bottom>\<close> of true.
\<close>
fun wf_fmla_c :: "ast_domain \<Rightarrow> ('ent \<rightharpoonup> type) \<Rightarrow> ('ent atom) formula \<Rightarrow> bool" where
  "wf_fmla_c D ty_ent (Atom a) \<longleftrightarrow> wf_atom_c D ty_ent a"
| "wf_fmla_c D ty_ent (\<bottom>) \<longleftrightarrow> True"
| "wf_fmla_c D ty_ent (\<phi>1 \<^bold>\<and> \<phi>2) \<longleftrightarrow> (wf_fmla_c D ty_ent \<phi>1 \<and> wf_fmla_c D ty_ent \<phi>2)"
| "wf_fmla_c D ty_ent (\<phi>1 \<^bold>\<or> \<phi>2) \<longleftrightarrow> (wf_fmla_c D ty_ent \<phi>1 \<and> wf_fmla_c D ty_ent \<phi>2)"
| "wf_fmla_c D ty_ent (\<^bold>\<not>\<phi>) \<longleftrightarrow> wf_fmla_c D ty_ent \<phi>"
| "wf_fmla_c D ty_ent (\<phi>1 \<^bold>\<rightarrow> \<phi>2) \<longleftrightarrow> (wf_fmla_c D ty_ent \<phi>1 \<and> wf_fmla_c D ty_ent \<phi>2)"

text \<open>Special case for a well-formed atomic predicate formula\<close>
fun wf_fmla_atom_c where
  "wf_fmla_atom_c D ty_ent (Atom (predAtm a vs)) \<longleftrightarrow> wf_pred_atom_c D ty_ent (a,vs)"
| "wf_fmla_atom_c D ty_ent _ \<longleftrightarrow> False"

text \<open>An effect is well-formed if the added and removed formulas
  are atomic\<close> (* ... are predicate atoms! Eq-Atoms not included. *)
fun wf_effect_c where
  "wf_effect_c D ty_ent (Effect a d) \<longleftrightarrow>
      (\<forall>ae\<in>set a. wf_fmla_atom_c D ty_ent ae)
    \<and> (\<forall>de\<in>set d.  wf_fmla_atom_c D ty_ent de)"


fun wf_action_schema_c :: "ast_domain \<Rightarrow> ast_action_schema \<Rightarrow> bool" where
    "wf_action_schema_c D (Action_Schema n params pre eff) \<longleftrightarrow> (
      let
        tyt = ty_term (map_of params) (map_of (consts D))
      in
        distinct (map fst params)
      \<and> wf_fmla_c D tyt pre
      \<and> wf_effect_c D tyt eff)"

fun wf_type_c where
    "wf_type_c D (Either Ts) \<longleftrightarrow> set Ts \<subseteq> insert ''object'' (fst`set (types D))"
fun wf_predicate_decl_c where
    "wf_predicate_decl_c D (PredDecl p Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. wf_type_c D T)"
definition "wf_types_c D \<equiv> snd`set (types D) \<subseteq> insert ''object'' (fst`set (types D))"

definition wf_domain_c :: "ast_domain \<Rightarrow> bool" where
    "wf_domain_c D \<equiv>
      wf_types_c D
    \<and> distinct (map predicate_decl.pred (predicates D))
    \<and> (\<forall>p\<in>set (predicates D). wf_predicate_decl_c D p)
    \<and> distinct (map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (consts D). wf_type_c D T)
    \<and> distinct (map ast_action_schema.name (actions D))
    \<and> (\<forall>a\<in>set (actions D). wf_action_schema_c D a)
    "

definition "objT_c P \<equiv> map_of (objects P) ++ map_of (consts (domain P))"

definition wf_world_model_c where
    "wf_world_model_c P M = (\<forall>f\<in>M. wf_fmla_atom_c (domain P) (objT_c P) f)"

definition wf_problem_c where
    "wf_problem_c P \<equiv>
      wf_domain_c (domain P)
    \<and> distinct (map fst (objects P) @ map fst (consts (domain P)))
    \<and> (\<forall>(n,T)\<in>set (objects P). wf_type_c (domain P) T)
    \<and> distinct (init P)
    \<and> wf_world_model_c P (set (init P))
    \<and> wf_fmla_c (domain P) (objT_c P) (goal P)
    "

subsection \<open> Execution \<close>

definition "is_obj_of_type_c P n T \<equiv> case (objT_c P) n of
    None \<Rightarrow> False
  | Some oT \<Rightarrow> of_type_c (domain P) oT T"

fun apply_effect_c :: "object ast_effect \<Rightarrow> world_model \<Rightarrow> world_model"
  where
     "apply_effect_c (Effect a d) s = (s - set d) \<union> (set a)"

fun subst_term_c where
    "subst_term_c psubst (term.VAR x) = psubst x"
  | "subst_term_c psubst (term.CONST c) = c"

fun instantiate_action_schema_c
    :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> ground_action"
  where
    "instantiate_action_schema_c (Action_Schema n params pre eff) args = (let
        tsubst = subst_term_c (the \<circ> (map_of (zip (map fst params) args)));
        pre_inst = (map_formula o map_atom) tsubst pre;
        eff_inst = (map_ast_effect) tsubst eff
      in
        Ground_Action pre_inst eff_inst
      )"

definition resolve_action_schema_c :: "ast_domain \<Rightarrow> name \<rightharpoonup> ast_action_schema" where
    "resolve_action_schema_c D n = index_by ast_action_schema.name (actions D) n"

fun resolve_instantiate_c :: "ast_domain \<Rightarrow> plan_action \<Rightarrow> ground_action" where
    "resolve_instantiate_c D (PAction n args) =
      instantiate_action_schema_c
        (the (resolve_action_schema_c D n))
        args"

definition execute_plan_action_c :: "ast_problem \<Rightarrow> plan_action \<Rightarrow> world_model \<Rightarrow> world_model"
    where "execute_plan_action_c P \<pi> M
      = (apply_effect_c (effect (resolve_instantiate_c (domain P) \<pi>)) M)"

(* This one doesn't exist in PDDL_STRIPS_Semantics *)
definition execute_plan_c :: "ast_problem \<Rightarrow> plan_action list \<Rightarrow> world_model \<Rightarrow> world_model"
  where "execute_plan_c P \<pi>s s = fold (execute_plan_action_c P) \<pi>s s"

definition "action_params_match_c P a args
    \<equiv> list_all2 (is_obj_of_type_c P) args (map snd (parameters a))"

fun wf_effect_inst_c :: "ast_problem \<Rightarrow> object ast_effect \<Rightarrow> bool" where
    "wf_effect_inst_c P (Effect (a) (d))
      \<longleftrightarrow> (\<forall>a\<in>set a \<union> set d. wf_fmla_atom_c (domain P) (objT_c P) a)"

fun wf_plan_action_c :: "ast_problem \<Rightarrow> plan_action \<Rightarrow> bool" where
    "wf_plan_action_c P (PAction n args) = (
      case resolve_action_schema_c (domain P) n of
        None \<Rightarrow> False
      | Some a \<Rightarrow>
          action_params_match_c P a args
        \<and> wf_effect_inst_c P (effect (instantiate_action_schema_c a args))
        )"

(* this isn't used in any function in the original theory*)
definition plan_action_enabled_c :: "ast_problem \<Rightarrow> plan_action \<Rightarrow> world_model \<Rightarrow> bool" where
    "plan_action_enabled_c P \<pi> M
      \<longleftrightarrow> wf_plan_action_c P \<pi> \<and> M \<^sup>c\<TTurnstile>\<^sub>\<equiv> precondition (resolve_instantiate_c (domain P) \<pi>)"

(* this is highly modified from the original *)
fun valid_plan_from_c :: "ast_problem \<Rightarrow> world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from_c P M [] = M \<^sup>c\<TTurnstile>\<^sub>\<equiv> (goal P)" |
    "valid_plan_from_c P M (\<pi> # \<pi>s) = (plan_action_enabled_c P \<pi> M \<and>
      valid_plan_from_c P (execute_plan_action_c P \<pi> M) \<pi>s)"

definition valid_plan_c :: "ast_problem \<Rightarrow> plan \<Rightarrow> bool" where
  "valid_plan_c P \<pi>s \<equiv> valid_plan_from_c P (set (init P)) \<pi>s" 

end