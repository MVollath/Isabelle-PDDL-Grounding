theory STRIPS_Sema_Supplement
  imports "Verified_SAT_Based_AI_Planning.STRIPS_Semantics"
begin

locale strips =
  fixes \<Pi> :: "'a strips_problem"

locale valid_strips = strips +
  assumes "is_valid_problem_strips \<Pi>"


end