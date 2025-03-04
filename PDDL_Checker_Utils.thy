theory PDDL_Checker_Utils
  imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Checker"
begin

abbreviation "of_type_x D oT T \<equiv> of_type_impl (ast_domain.STG D) oT T"

abbreviation "wf_domain_x D \<equiv> ast_domain.wf_domain' D (ast_domain.STG D) (ast_domain.mp_constT D)"

abbreviation "wf_problem_x P \<equiv>
  let D = domain P in
  ast_problem.wf_problem' P (ast_domain.STG D) (ast_domain.mp_constT D) (ast_problem.mp_objT P)"

(* this just directly displays the first error if applicable *)
fun reveal_error :: "(unit \<Rightarrow> char list \<Rightarrow> char list) + 'a \<Rightarrow> char list + 'a" where
  "reveal_error (Inl e) = Inl (e () [])" |
  "reveal_error (Inr x) = Inr x"

abbreviation "enab_exec_x P pa s \<equiv>
  let D = domain P in reveal_error( 
  ast_problem.en_exE2 P (ast_domain.STG D) (ast_problem.mp_objT P) pa s)"

abbreviation "check_wf_domain_x D \<equiv> reveal_error (
  check_wf_domain D (ast_domain.STG D) (ast_domain.mp_constT D))"

abbreviation "valid_plan_x P \<pi>s \<equiv>
  let D = domain P;
      stg = ast_domain.STG D;
      obT = ast_problem.mp_objT P;
      i = ast_problem.I P in
  reveal_error (ast_problem.valid_plan_fromE P stg obT 1 i \<pi>s)"





end