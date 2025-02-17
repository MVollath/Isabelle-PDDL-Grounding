theory String_Shenanigans
imports Main "Show.Show_Instances"
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

lemma dist_prefix: "distinct xs \<Longrightarrow> distinct (map ((@) (safe_prefix ys)) xs)"
  by (simp add: distinct_conv_nth)


(* padding *)

definition pad :: "nat \<Rightarrow> string \<Rightarrow> string" where
  "pad n s \<equiv> s @ replicate (n - length s) (CHR ''_'')"

lemma pad_length:
  "n \<ge> length s \<Longrightarrow> length (pad n s) = n"
  "length (pad n s) \<ge> n"
  "length (pad n s) \<ge> length s"
  unfolding pad_def by simp_all

definition make_unique :: "string list \<Rightarrow> string \<Rightarrow> string" where
  "make_unique ss s \<equiv> pad (max_length ss + 1) s"

lemma made_unique: "make_unique ss x \<notin> set ss"
proof -
  have "max_length ss + 1 \<le> length (make_unique ss x)"
    using make_unique_def pad_length(2) by simp
  hence "\<forall>s \<in> set ss. length s < length (make_unique ss x)"
    using max_length_correct by fastforce
  thus ?thesis by auto
qed


definition pad_strings :: "string list \<Rightarrow> string list" where
  "pad_strings ss \<equiv> map (pad (max_length ss + 1)) ss"

lemma
  assumes "distinct xs"
    "\<forall>y \<in> set ys. length y = n"
  shows "distinct (map2 (@) ys xs)"
  using assms oops

lemma show_nat_inj: fixes a :: nat and b :: nat assumes "a \<noteq> b" shows "show a \<noteq> show b"
  using assms sorry

fun nat_upto :: "nat \<Rightarrow> nat list" where
  "nat_upto 0 = [0]" |
  "nat_upto (Suc n) = Suc n # nat_upto n"

definition "distinct_strings n \<equiv> map show (case n of 0 \<Rightarrow> [] | Suc m \<Rightarrow> nat_upto m)"


lemma dist_str_props:
  "length (distinct_strings n) = n"
  "distinct (distinct_strings n)"
  sorry


definition distinctize :: "string list \<Rightarrow> string list \<Rightarrow> string list" where
  "distinctize blocked new \<equiv>
    map (append (safe_prefix blocked)) new"

(*lemma distinctize_correct:
  "disjnt (set blocked) (set (distinctize blocked new))"
  by (metis (no_types, opaque_lifting) disjnt_iff distinctize_def ex_map_conv safe_prefix_correct)*)


end