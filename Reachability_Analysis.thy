theory Reachability_Analysis
  imports PDDL_Sema_Supplement Solve_Datalog Normalization_Definitions
begin

subsection \<open> Code \<close>
(*
datatype (preds_rh: 'p,'x,'c) rh = 
  Eql "('x,'c) id" "('x,'c) id" ("_ \<^bold>= _" [61, 61] 61)
  | Neql "('x,'c) id" "('x,'c) id" ("_ \<^bold>\<noteq> _" [61, 61] 61)
  | PosLit 'p "('x,'c) id list" ("\<^bold>+ _ _" [61, 61] 61)
  | NegLit 'p "('x,'c) id list" ("\<^bold>\<not> _ _" [61, 61] 61)
*)
(* Cls 'p "('x,'c) id list" (the_rhs: "('p,'x,'c) rh list") *)

type_synonym dl_id = "(name, name) id"
type_synonym dl_rh = "(name, name, name) rh"
type_synonym dl_clause = "(name, name, name) Datalog.clause"
type_synonym name_dl_program = "(name, name, name) dl_program"

abbreviation (input) "pname p \<equiv> CHR ''P'' # predicate.name p"
abbreviation (input) "aname n \<equiv> CHR ''A'' # n"
abbreviation (input) "tname \<equiv> ''+''"
abbreviation (input) "fname \<equiv> ''-''"
abbreviation tfact :: "dl_clause" where
  "tfact \<equiv> Cls tname [] []"

fun ac_arg :: "(variable \<times> type) \<Rightarrow> (name, name) id" where
  "ac_arg (Var x, _) = id.Var x"

abbreviation ac_args :: "(variable \<times> type) list \<Rightarrow> (name, name) id list" where
  "ac_args args \<equiv> map ac_arg args"

fun p_arg :: "term \<Rightarrow> dl_id" where
  "p_arg (term.VAR (Var x)) = id.Var x" |
  "p_arg (term.CONST (Obj x)) = id.Cst x"

abbreviation p_args :: "term list \<Rightarrow> dl_id list" where
  "p_args xs \<equiv> map p_arg xs"

(* expects is_lit_pos *)
term is_lit_pos
fun lit_rh :: "term atom formula \<Rightarrow> dl_rh" where
  "lit_rh \<bottom> = \<^bold>+ fname []" |
  "lit_rh (\<^bold>\<not>\<bottom>) = \<^bold>+ tname []" |
  "lit_rh (Atom (predAtm n args)) = \<^bold>+ (pname n) (p_args args)" |
  "lit_rh (Atom (Eq a b)) = p_arg a \<^bold>= p_arg b" |
  "lit_rh (\<^bold>\<not> (Atom (Eq a b))) = p_arg a \<^bold>\<noteq> p_arg b" (* not yet supported btw *)

(* expects is_pos_conj *)
definition pre_clauses :: "term atom formula \<Rightarrow> dl_rh list" where
  "pre_clauses F = map lit_rh (un_and F)"

fun app_clause :: "ast_action_schema \<Rightarrow> dl_clause" where
  "app_clause (Action_Schema n args pre eff) =
    Cls (aname n) (ac_args args) (pre_clauses pre)"

(* expects is_predAtom *)
fun add_eff_clause :: "name \<Rightarrow> term atom formula \<Rightarrow> dl_clause" where
  "add_eff_clause n (Atom (predAtm p args)) = undefined"

fun eff_clauses :: "ast_action_schema \<Rightarrow> dl_clause list" where
  "eff_clauses (Action_Schema n args pre (Effect add del)) =
    map (add_eff_clause n) add"

definition ac_clauses :: "ast_action_schema \<Rightarrow> dl_clause list" where
  "ac_clauses ac = app_clause ac # eff_clauses ac"

context ast_problem begin

definition reach_clauses :: "dl_clause list" where
  "reach_clauses \<equiv> tfact # concat (map ac_clauses (actions D))"

definition reachability_program :: "name_dl_program" where
  "reachability_program \<equiv> set reach_clauses"

lemmas reach_program_defs = reach_clauses_def reachability_program_def


end

definition (in ast_problem) "lmao\<equiv>False"
lemmas reachability_code =
  ast_problem.lmao_def
declare reachability_code[code]



subsection \<open> Proofs \<close>

context wf_relaxed_normed_prob begin


end


end