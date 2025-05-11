theory PDDL_to_STRIPS
  imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    "AI_Planning_Languages_Semantics.Option_Monad_Add"
    "Verified_SAT_Based_AI_Planning.STRIPS_Semantics"
    PDDL_Sema_Supplement Normalization_Definitions
    Utils Formula_Utils (* String_Shenanigans *)
begin


(* utils *)
fun map_filter :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_filter f [] = []" |
  "map_filter f (x # xs) = (case f x of None \<Rightarrow> map_filter f xs |
    Some y \<Rightarrow> y # map_filter f xs)"

context ast_problem begin

fun as_strips_var_p :: "predicate_decl \<Rightarrow> name" where
  "as_strips_var_p (PredDecl (Pred n) args) = CHR ''+'' # n"
fun as_strips_var_n :: "predicate_decl \<Rightarrow> name" where
  "as_strips_var_n (PredDecl (Pred n) args) = CHR ''-'' # n"
term Option.bind

(* expects input to satisfy \<open>is_predAtom\<close> *)
fun as_strips_atom_p :: "'a atom formula \<Rightarrow> name" where
  "as_strips_atom_p (Atom (predAtm (Pred p) args)) = CHR ''+'' # p"
fun as_strips_atom_n :: "'a atom formula \<Rightarrow> name" where
  "as_strips_atom_n (Atom (predAtm (Pred p) args)) = CHR ''-'' # p"

term is_conj
term is_lit_plus
(* todo, maybe use monads here? *)
term omap
fun (in -)option_Cons :: "'a option \<Rightarrow> 'a list option \<Rightarrow> 'a list option" where
  "option_Cons _ None = None" |
  "option_Cons None (Some xs) = None" |
  "option_Cons (Some x) (Some xs) = Some (x # xs)"

(*(* expects \<open>is_lit_plus\<close> but no Eq allowed *)
fun as_strips_var :: "term atom formula \<rightharpoonup> name" where
  "as_strips_pre \<bottom> = None" |
  "as_strips_pre (\<^bold>\<not>\<bottom>) = Some []" |
  "as_strips_pre (Atom a) = Some ([as_strips_atom_p (Atom a)])" *)

(* expects \<open>is_conj p \<and> no_Eq p\<close> *)
fun as_strips_pre :: "'a atom formula \<rightharpoonup> name list" where
  "as_strips_pre \<bottom> = None" |
  "as_strips_pre (\<^bold>\<not>\<bottom>) = Some []" |
  "as_strips_pre (Atom a) = Some ([as_strips_atom_p (Atom a)])" |
  "as_strips_pre (\<^bold>\<not>(Atom a)) = Some ([as_strips_atom_n (Atom a)])" |
  "as_strips_pre (A \<^bold>\<and> B) = (case (as_strips_pre B) of None \<Rightarrow> None |
    Some ys \<Rightarrow> (case (as_strips_pre A) of None \<Rightarrow> None |
    Some y \<Rightarrow> Some (y @ ys)))"

fun as_strips_op :: "ast_action_schema \<rightharpoonup> name strips_operator" where
  "as_strips_op (Action_Schema n args pre (Effect add del)) =
    (case as_strips_pre pre of None \<Rightarrow> None |
    Some pre' \<Rightarrow> Some \<lparr>
    precondition_of = pre'
    , add_effects_of = map as_strips_atom_p add @ map as_strips_atom_n del
    , delete_effects_of = map as_strips_atom_p del @ map as_strips_atom_n add \<rparr>)"

term fold

(* first set every variable to false *)
(* then update those in init *)
definition var_map :: "(name, bool) state" where
  "var_map \<equiv>
  (let ps = map as_strips_var_p (predicates D); ns = map as_strips_var_n (predicates D);
    spos = fold (\<lambda>v c. c(v := Some False)) ps (\<lambda>x. None) in
    fold (\<lambda>v c. c(v := Some True)) ns spos)"

fun as_strips_init :: "(name, bool) state \<Rightarrow> 'a atom formula list \<Rightarrow> (name, bool) state" where
  "as_strips_init c [] = c" |
  "as_strips_init c (i # is) = (as_strips_init c is)(as_strips_atom_p i := Some True, as_strips_atom_n i := Some False)"

(* expects \<open>is_conj p \<and> no_Eq p\<close> *)
fun as_strips_goal :: "'a atom formula \<rightharpoonup> (name \<times> bool) list" where
  "as_strips_goal \<bottom> = None" |
  "as_strips_goal (\<^bold>\<not>\<bottom>) = Some []" |
  "as_strips_goal (Atom a) = Some [(as_strips_atom_p (Atom a), True)]" |
  "as_strips_goal (\<^bold>\<not>(Atom a)) = Some[(as_strips_atom_p (Atom a), False)]" |
  "as_strips_goal (A \<^bold>\<and> B) = do {xs \<leftarrow> as_strips_goal A; ys \<leftarrow> as_strips_goal B; Some (xs @ ys)}"

(* eliminate contradictions *)
fun (in -) unique_mapof :: "(name \<times> bool) list \<rightharpoonup> (name, bool) state" where
  "unique_mapof [] = Some (\<lambda>_. None)" |
  "unique_mapof ((x, b) # xs) =
    do {m \<leftarrow> unique_mapof xs; if m x = Some (\<not>b) then None else Some (m(x\<mapsto>b))}"

definition as_strips :: "name strips_problem" where
  "as_strips \<equiv> \<lparr> 
    variables_of = map as_strips_var_p (predicates D) @
      map as_strips_var_n (predicates D)
    , operators_of = map_filter as_strips_op (actions D)
    , initial_of = as_strips_init var_map (init P)
    , goal_of = the (unique_mapof (the (as_strips_goal (goal P)))) \<rparr>"

end

lemmas to_strips_code =
  ast_problem.as_strips_var_p.simps
  ast_problem.as_strips_var_n.simps
  ast_problem.as_strips_atom_p.simps
  ast_problem.as_strips_atom_n.simps
  ast_problem.as_strips_pre.simps
  ast_problem.as_strips_op.simps
  ast_problem.as_strips_init.simps
  ast_problem.var_map_def
  ast_problem.as_strips_goal.simps
  ast_problem.as_strips_def
declare to_strips_code[code]

end