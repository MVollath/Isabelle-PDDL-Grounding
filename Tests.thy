theory Tests
  imports Main
    "../LTS-formalization/Datalog/Datalog"
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    "Show.Show"
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Checker"
begin

(* define single entailment \<TTurnstile>\<^sub>1 :: formula \<Rightarrow> formula \<Rightarrow> bool *)


definition fmla_entailment :: "'a formula \<Rightarrow> 'a formula \<Rightarrow> bool" ("(_ \<TTurnstile>\<^sub>1/ _)" [53,53] 53) where
  "F \<TTurnstile>\<^sub>1 G \<equiv> \<forall>\<A>. \<A> \<Turnstile> F \<longrightarrow> \<A> \<Turnstile> G"

value "shows ''kh'' ''lmao''"

(*interpretation xd : ast_problem "Problem (Domain [] [] [] []) [] [] \<bottom>" .*)

end