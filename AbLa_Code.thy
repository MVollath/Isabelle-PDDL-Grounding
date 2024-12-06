theory AbLa_Code
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
begin

text \<open>A hacky way to make the functions in PDDL_STRIPS_Semantics executable.\<close>

(* suffix _c for "code" *)

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


end