theory Precondition_Normalization
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    PDDL_Sema_Supplement Utils String_Shenanigans DNF
begin

definition "n_clauses ac \<equiv> length (dnf_list (ast_action_schema.precondition ac))"

context ast_domain begin

definition "max_n_clauses \<equiv> Max (set (map n_clauses (actions D)))"
definition "prefix_padding \<equiv> max_length (distinct_strings max_n_clauses) + 1"

fun (in -) set_n_pre :: " ast_action_schema \<Rightarrow> string \<Rightarrow> term atom formula \<Rightarrow> ast_action_schema" where
  "set_n_pre (Action_Schema _ params _ eff) n pre
  = Action_Schema n params pre eff"

definition "split_ac_names ac n \<equiv>
  map (\<lambda>prefix. pad prefix_padding prefix @ ac_name ac) (distinct_strings n)"

definition split_ac :: "ast_action_schema \<Rightarrow> ast_action_schema list" where
  "split_ac ac =
    (let clauses = dnf_list (ac_pre ac) in
    map2 (set_n_pre ac) (split_ac_names ac (length clauses)) clauses)"

definition "split_acs \<equiv> concat (map split_ac (actions D))"

definition "split_dom \<equiv>
  Domain
    (types D)
    (predicates D)
    (consts D)
    split_acs"

definition (in ast_problem) "split_prob \<equiv>
  Problem
    split_dom
    (objects P)
    (init P)
    (goal P)"

(* it's important to be able to convert a plan for the output problem into a plan for the input problem.
  The other direction is probably (hopefully?) not important. *)
fun restore_pa_split where
  "restore_pa_split (PAction n args) = PAction (drop prefix_padding n) args"
abbreviation "restore_plan_split \<pi>s \<equiv> map restore_pa_split \<pi>s"

definition (in ast_domain) "precond_normed_dom \<equiv>
  \<forall>ac \<in> set (actions D). is_conj (ac_pre ac)"

definition (in ast_problem) "precond_normed_prob \<equiv> precond_normed_dom"

end

section \<open> Precondition Normalization Proofs \<close>

text \<open> locale setup for simplified syntax \<close>

abbreviation (in ast_domain) (input) "D4 \<equiv> split_dom"
abbreviation (in ast_problem) (input) "P4 \<equiv> split_prob"

locale ast_domain4 = ast_domain
sublocale ast_domain4 \<subseteq> d4: ast_domain D4 .

locale wf_ast_domain4 = wf_ast_domain
sublocale wf_ast_domain4 \<subseteq> d4: ast_domain D4 .
sublocale wf_ast_domain4 \<subseteq> ast_domain4 .

locale ast_problem4 = ast_problem
sublocale ast_problem4 \<subseteq> p4: ast_problem P4 .
sublocale ast_problem4 \<subseteq> ast_domain4 D .

locale wf_ast_problem4 = wf_ast_problem
sublocale wf_ast_problem4 \<subseteq> p4 : ast_problem P4.
sublocale wf_ast_problem4 \<subseteq> ast_problem4 .
sublocale wf_ast_problem4 \<subseteq> wf_ast_domain4 D
  by unfold_locales

text \<open> Alternate definitions \<close>

(* probably unnecessary *)
lemma set_n_pre_alt: "set_n_pre ac n pre =
  Action_Schema n (ac_params ac) pre (ac_eff ac)"
  by (cases ac) simp

(* probably unnecessary *)
lemma set_n_pre_sel [simp]:
  "ac_name (set_n_pre ac n pre) = n"
  "ac_params (set_n_pre ac n pre) = ac_params ac"
  "ac_pre (set_n_pre ac n pre) = pre"
  "ac_eff (set_n_pre ac n pre) = ac_eff ac"
  using set_n_pre_alt by simp_all

thm ast_domain.split_ac_def

lemma
  "i < length as \<Longrightarrow> i < length bs \<Longrightarrow> map2 f as bs ! i = f (as!i) (bs!i)"
  by simp

lemma (in ast_domain)
  assumes "i < length (dnf_list (ac_pre ac))"
  shows "split_ac ac ! i =
    set_n_pre ac
    ((\<lambda>prefix. pad prefix_padding prefix @ ac_name ac) (distinct_strings (length (dnf_list (ac_pre ac))) ! i))
    (dnf_list (ac_pre ac) ! i)"
  using assms unfolding split_ac_def split_ac_names_def set_n_pre_alt Let_def sorry

lemma (in ast_domain) split_dom_sel [simp]:
  "types D4 = types D"
  "predicates D4 = predicates D"
  "consts D4 = consts D"
  "actions D4 = split_acs"
  using split_dom_def by simp_all

lemma (in ast_problem) split_prob_sel [simp]:
  "domain P4 = D4"
  "objects P4 = objects P"
  "init P4 = init P"
  "goal P4 = goal P"
  using split_prob_def by simp_all


subsection \<open> Output format \<close>

context ast_problem4 begin
thm precond_normed_dom_def
(* \<forall>ac \<in> set (actions D). is_conj (ac_pre ac) *)

thm split_ac_def
lemma prec_normed_ac:
  "\<forall>ac' \<in> set (split_ac ac). is_conj (ac_pre ac')"
proof -
  have "\<forall>c \<in> set (dnf_list (ac_pre ac)). is_conj c"
    using dnf_list_conjs by auto
  have "\<forall>ac' \<in> set (split_ac ac). ac_pre ac \<in>
    set (dnf_list (ac_pre ac))" unfolding split_ac_def Let_def sorry
  thus ?thesis
    unfolding split_ac_def Let_def sorry
qed

end

subsection \<open> Code Setup \<close>

lemmas precond_norm_code =
  n_clauses_def
  ast_domain.max_n_clauses_def
  ast_domain.prefix_padding_def
  ast_domain.split_ac_names_def
  ast_domain.split_ac_def
  ast_domain.split_acs_def
  ast_domain.split_dom_def
  ast_problem.split_prob_def
  ast_domain.restore_pa_split.simps
declare precond_norm_code[code]

end