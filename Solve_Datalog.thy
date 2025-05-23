theory Solve_Datalog
  imports "../LTS-formalization/Datalog/Datalog" Utils
begin

text \<open> random testing \<close>
thm exi_least_solution
thm least_iff_minimal

term strat_wf
term solves_program
term solves_cls

term lh_consequence

term Cls

abbreviation  "dl2 == Cls ''p'' [id.Var ''x'', id.Cst ''y'']
  [id.Var ''x'' \<^bold>= id.Var ''y'', \<^bold>+ ''q'' [], \<^bold>+ ''h'' []]"
value "strat_wf (\<lambda>x. 0) {dl2}"

subsection \<open> solving \<close>

type_synonym ('p, 'c) fact = "('p \<times> 'c list)"
(* not so sure what datatype I want yet *)
type_synonym ('p, 'c) fact_orga = "('p \<Rightarrow> 'c list list)"
type_synonym ('p, 'x, 'c) list_dl = "('p, 'x, 'c) clause list"

datatype ('p,'x,'c) clause2 = Cls2 'p "('x,'c) id list"
  (the_pos: "('p,'x,'c) rh list") (the_conds: "('p,'x,'c) rh list")


locale datalog =
  fixes D :: "('p, 'x, 'c) list_dl"
begin

fun rh_preds where
  "rh_preds [] = []" |
  "rh_preds (PosLit p args # rhs) = p # rh_preds rhs" |
  "rh_preds (NegLit p args # rhs) = p # rh_preds rhs" |
  "rh_preds (l # rhs) = rh_preds rhs"

fun cls_preds where
  "cls_preds (Cls p args rhs) = p # rh_preds rhs"

definition "preds \<equiv> remdups (concat (map cls_preds D))"

definition (in -) facts_for_pred :: "('p, 'c) fact_orga \<Rightarrow> 'p \<Rightarrow> ('p, 'c) fact list"where
  "facts_for_pred fo p \<equiv> map (Pair p) (fo p)"

definition as_facts :: "('p, 'c) fact_orga \<Rightarrow> ('p, 'c) fact list" where
  "as_facts fo = concat (map (facts_for_pred fo) preds)"

fun is_PosLit :: "('p, 'x, 'c) rh \<Rightarrow> bool" where
  "is_PosLit (PosLit p args) = True" |
  "is_PosLit _ = False"

fun as_clause2 :: "('p,'x,'c) clause \<Rightarrow> ('p,'x,'c) clause2" where
  "as_clause2 (Cls p args rh) =
    Cls2 p args (filter is_PosLit rh) (filter (Not \<circ> is_PosLit) rh)"

end

term list_update

fun facts_of :: "('p \<times> 'c list list) \<Rightarrow> ('p, 'c) fact list" where
  "facts_of (p, cs) = map (Pair p) cs"



fun solve_dl :: "('p,'x,'c) list_dl \<Rightarrow> ('p,'c) fact_orga" where
  "solve_dl dl = undefined"

subsection \<open> Invariants \<close>

subsection \<open> PROOF \<close>


(* TODO: this shouldn't really return option ever if invars hold *)
fun setof_opn :: "'a list option \<Rightarrow> 'a set" where
  "setof_opn None = {}" |
  "setof_opn (Some xs) = set xs"

(* assumes distinct (map fst fo) *)
definition as_pred_val :: "('p, 'c) fact_orga \<Rightarrow> ('p,'c) pred_val" where
  "as_pred_val fo = setof_opn \<circ> (map_of fo)"

lemma solves_fact: "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args [] \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>l\<^sub>h (p, args)"
  unfolding solves_cls_def by auto

theorem dl_solved: "as_pred_val (solve_dl dl) \<Turnstile>\<^sub>d\<^sub>l set dl"
  oops




subsection \<open> alternative solving \<close>
definition solve_dl_consts :: "('p,'x,'c) dl_program \<Rightarrow> 'c list \<Rightarrow> ('p,'x,'c) lh list" where
  "solve_dl_consts \<equiv> undefined"


subsection \<open> defining positive dl \<close>

fun pos_rh where
  "pos_rh (\<^bold>\<not> p args) = False" |
  "pos_rh rh = True"

fun pos_clause where
  "pos_clause (Cls p args rh) = list_all1 pos_rh rh"

definition "pos_dl dl \<equiv> \<forall>c \<in> dl. pos_clause c"

(* prove pure positive DL is strat_wf *)
lemma pos_clause_strat:
  assumes "pos_clause c"
  shows "strat_wf_cls (\<lambda>x. 0) c"
proof -
  have "rnk (\<lambda>x. 0) x = 0" if "pos_rh x" for x
    using that by (cases x) simp_all
  thus ?thesis using assms by (cases c) auto
qed

lemma pos_dl_strat:
  assumes "pos_dl dl"
  shows "strat_wf (\<lambda>x. 0) dl"
  using assms unfolding pos_dl_def strat_wf_def
  using pos_clause_strat by blast

subsection \<open> defining wf DL \<close>

term vars_lh

subsection \<open> minimal solution props\<close>

(* pos minimal solution *)



(* better solution datatypes *)
(* construct solution *)



end