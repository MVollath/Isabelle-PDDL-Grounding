theory String_Shenanigans
imports Main "Show.Show_Instances"
begin

fun max_length :: "'a list list \<Rightarrow> nat" where
  "max_length [] = 0" | (* yeah, yeah, technically it should be -1 or None/undefined or something *)
  "max_length (xs # xss) = max (length xs) (max_length xss)"

thm Max_insert
term  finite
thm card_eq_0_iff

(*lemma "card xs \<noteq> 0 \<Longrightarrow> Max (insert x xs) = max x (Max xs)"
  by (metis Max_insert card.infinite card_0_eq)
  by (simp add: card_eq_0_iff)*)

(*lemma "length xss > 0 \<Longrightarrow> max_length xss = Max (set (map length xss))"
  apply (induction xss) apply simp
  using Max_insert card_eq_0_iff card_0_eq *)

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

definition pad_l :: "nat \<Rightarrow> string \<Rightarrow> string" where
  "pad_l n s \<equiv> replicate (n - length s) (CHR ''_'') @ s"

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

fun nat_upto_help :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "nat_upto_help 0 build = 0 # build" |
  "nat_upto_help (Suc n) build = nat_upto_help n (Suc n # build)"

definition "nat_upto n \<equiv> nat_upto_help n []"

lemma nat_upto_help_length: "length (nat_upto_help n xs) = n + 1 + length xs"
  by (induction n arbitrary: xs) simp_all

lemma nat_upto_length [simp]: "length (nat_upto n) = n + 1"
  unfolding nat_upto_def using nat_upto_help_length by simp

lemma nat_upto_help_aux: "nat_upto_help n (xs@ys) = nat_upto_help n xs @ ys"
proof (induction n arbitrary: xs)
  case (Suc n)
  have "nat_upto_help (Suc n) (xs @ ys) = nat_upto_help n ((Suc n # xs) @ ys)" by simp
  also have "... = nat_upto_help n (Suc n # xs) @ ys" using Suc.IH by blast
  also have "... = nat_upto_help (Suc n) xs @ ys" by simp
  finally show ?case by simp
qed simp

lemma "(xs @ [y]) ! length xs = y" by simp

lemma nat_upto_help_nth: assumes "i \<le> n" shows "nat_upto_help n xs ! i = i"
using assms proof (induction n arbitrary: i xs)
  case (Suc n)
  then consider "i \<le> n" | "i = Suc n" using le_SucE by blast
  thus ?case
  proof (cases)
    case 2
    have "nat_upto_help (Suc n) xs = nat_upto_help n ([] @ (Suc n # xs))" by simp
    also have "... = nat_upto_help n [] @ (Suc n # xs)" using nat_upto_help_aux by metis
    finally have "nat_upto_help (Suc n) xs ! i = (nat_upto_help n [] @ (Suc n # xs)) ! (length (nat_upto_help n []))"
      using 2 nat_upto_help_length by simp
    thus ?thesis using 2 by simp
  qed (simp add: Suc)
qed simp

lemma nat_upto_nth [simp]: assumes "i \<le> n" shows "nat_upto n ! i = i"
  using assms nat_upto_help_nth nat_upto_def by simp

lemma nat_upto_distinct: "distinct (nat_upto n)"
proof -
  have "nat_upto n ! i \<noteq> nat_upto n ! j" if "i \<noteq> j" "i \<le> n" "j \<le> n" for i j
    using nat_upto_nth that by simp
  moreover have "i \<le> n \<longleftrightarrow> i < length (nat_upto n)" for i by auto
  ultimately show ?thesis using distinct_conv_nth by blast
qed

definition "unique_string (i::nat) \<equiv> show i"
definition "distinct_strings n \<equiv> map unique_string (case n of 0 \<Rightarrow> [] | Suc m \<Rightarrow> nat_upto m)"

lemma show_nat_inj: fixes a :: nat and b :: nat assumes "a \<noteq> b" shows "show a \<noteq> show b"
  using assms sorry

lemma unique_str_bij:
  "i \<noteq> j \<longleftrightarrow> unique_string i \<noteq> unique_string j"
  using unique_string_def show_nat_inj by auto

lemma distinct_str_length [simp]: "length (distinct_strings n) = n"
  unfolding distinct_strings_def
  by (cases n) simp_all

lemma distinct_strings_nth [simp]:
  assumes "i < n" shows "distinct_strings n ! i = unique_string i"
  unfolding distinct_strings_def using assms by (cases n) simp_all

lemma distinct_strings_dist:
  "distinct (distinct_strings n)"
  using unique_str_bij distinct_conv_nth by fastforce


definition distinctize :: "string list \<Rightarrow> string list \<Rightarrow> string list" where
  "distinctize blocked new \<equiv>
    map (append (safe_prefix blocked)) new"

(*lemma distinctize_correct:
  "disjnt (set blocked) (set (distinctize blocked new))"
  by (metis (no_types, opaque_lifting) disjnt_iff distinctize_def ex_map_conv safe_prefix_correct)*)


end