theory String_Shenanigans
imports Main
begin

fun max_length :: "'a list list \<Rightarrow> nat" where
  "max_length [] = 0" | (* yeah, yeah, technically it should be -1 or None or something *)
  "max_length (xs # xss) = max (length xs) (max_length xss)"

lemma max_length_correct: "\<forall>s \<in> set ss. length s \<le> max_length ss"
  by (induction ss) auto

definition safe_prefix :: "string list \<Rightarrow> string" where
  "safe_prefix xs \<equiv> replicate (max_length xs + 1) (CHR ''_'')"

lemma safe_prefix_correct: "safe_prefix xs @ x \<notin> set xs"
  using max_length_correct safe_prefix_def by force

definition distinctize :: "string list \<Rightarrow> string list \<Rightarrow> string list" where
  "distinctize blocked new \<equiv>
    map (append (safe_prefix blocked)) new"

lemma distinctize_correct:
  "disjnt (set blocked) (set (distinctize blocked new))"
  by (metis (no_types, opaque_lifting) disjnt_iff distinctize_def ex_map_conv safe_prefix_correct)


end