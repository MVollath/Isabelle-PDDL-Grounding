theory PDDL_Instance_Relationships
imports PDDL_Sema_Supplement
begin

text \<open>This theory concerns itself mostly with relationships between two PDDL instances
  (domains or problems). They are of particular interest since the normalization steps produce
  new instances that retain some of the previous properties.\<close>

lemma co_fmla_wf:
  assumes "\<And>a. ast_domain.wf_atom d1 tyt1 a \<longrightarrow> ast_domain.wf_atom d2 tyt2 a"
  shows "ast_domain.wf_fmla d1 tyt1 \<phi> \<longrightarrow> ast_domain.wf_fmla d2 tyt2 \<phi>"
  using assms apply (induction \<phi>)
  using ast_domain.wf_fmla.simps apply metis+
  done

lemma co_fmla_atom_wf:
  assumes "\<And>a. ast_domain.wf_atom d1 tyt1 a \<longrightarrow> ast_domain.wf_atom d2 tyt2 a"
  shows "ast_domain.wf_fmla_atom d1 tyt1 \<phi> \<longrightarrow> ast_domain.wf_fmla_atom d2 tyt2 \<phi>"
  using assms co_fmla_wf ast_domain.wf_fmla_atom_alt by metis

lemma co_effect_wf:
  assumes "\<And>a. ast_domain.wf_atom d1 tyt1 a \<longrightarrow> ast_domain.wf_atom d2 tyt2 a"
  shows "ast_domain.wf_effect d1 tyt1 \<epsilon> \<longrightarrow> ast_domain.wf_effect d2 tyt2 \<epsilon>"
  using assms co_fmla_atom_wf ast_domain.wf_effect_alt by metis

lemma co_wm_wf:
  assumes "\<And>a. ast_domain.wf_atom (domain p1) (ast_problem.objT p1) a
    \<longrightarrow> ast_domain.wf_atom (domain p2) (ast_problem.objT p2) a"
  shows "ast_problem.wf_world_model p1 m \<longrightarrow> ast_problem.wf_world_model p2 m"
  using assms co_fmla_atom_wf ast_problem.wf_world_model_def by metis

lemmas co_wf = co_fmla_wf co_fmla_atom_wf co_effect_wf co_wm_wf

subsection \<open> Formula Preds \<close>

fun fmla_preds :: "'ent atom formula \<Rightarrow> predicate set" where
  "fmla_preds (Atom (predAtm p xs)) = {p}" |
  "fmla_preds (Atom (Eq a b)) = {}" |
  "fmla_preds \<bottom> = {}" |
  "fmla_preds (\<^bold>\<not> \<phi>) = fmla_preds \<phi>" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2" |
  "fmla_preds (\<phi>\<^sub>1 \<^bold>\<rightarrow> \<phi>\<^sub>2) = fmla_preds \<phi>\<^sub>1 \<union> fmla_preds \<phi>\<^sub>2"

lemma fmla_preds_alt: "fmla_preds \<phi> = {p | p xs. predAtm p xs \<in> atoms \<phi>}"
  apply (induction \<phi>)
  subgoal for x
    apply (cases x; simp_all)
    done
  by auto


lemma map_preserves_fmla_preds: "fmla_preds F = fmla_preds ((map_formula \<circ> map_atom) f F)"
proof (induction F)
  case (Atom x)
  thus ?case by (cases x) simp_all
qed auto

lemma notin_fmla_preds_notin_atoms: "p \<notin> fmla_preds \<phi> \<Longrightarrow> predAtm p args \<notin> atoms \<phi>"
  using fmla_preds_alt by blast


end