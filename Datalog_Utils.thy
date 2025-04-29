theory Datalog_Utils
  imports "../LTS-formalization/Datalog/Datalog"
begin

lemma solves_lh_lh_iff: "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s Cls p args [] \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>l\<^sub>h (p, args)"
  unfolding solves_cls_def by auto


end