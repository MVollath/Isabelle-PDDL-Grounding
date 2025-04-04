theory String_Shenanigans
imports Main "Show.Show_Instances" "HOL-Library.Sublist"
begin

fun max_length :: "'a list list \<Rightarrow> nat" where
  "max_length [] = 0" | (* yeah, yeah, technically it should be -1 or None/undefined or something *)
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

definition padl :: "nat \<Rightarrow> string \<Rightarrow> string" where
  "padl n s \<equiv> replicate (n - length s) (CHR ''_'') @ s"

lemma pad_length:
  "n \<ge> length s \<Longrightarrow> length (pad n s) = n"
  "length (pad n s) \<ge> n"
  "length (pad n s) \<ge> length s"
  unfolding pad_def by simp_all

lemma padl_length:
  "n \<ge> length s \<Longrightarrow> length (padl n s) = n"
  "length (padl n s) \<ge> n"
  "length (padl n s) \<ge> length s"
  unfolding padl_def by simp_all

lemma count_replicate: "count_list (replicate n x) x = n"
  by (induction n) simp_all

lemma count_pad:
  assumes "CHR ''_'' \<notin> set xs"
  shows "count_list (pad n xs) (CHR ''_'') = n - length xs"
  unfolding pad_def using assms count_replicate by fastforce

lemma count_padl:
  assumes "CHR ''_'' \<notin> set xs"
  shows "count_list (padl n xs) (CHR ''_'') = n - length xs"
  unfolding padl_def using assms count_replicate by fastforce

(* Omitting "n \<ge> length xs" "n \<ge> length ys" from assumptions because it's unnecessary*)
lemma pad_neq:
  assumes "(CHR ''_'') \<notin> set xs" "CHR ''_'' \<notin> set ys" "xs \<noteq> ys"
  shows "pad n xs \<noteq> pad n ys"
proof (cases "length xs = length ys")
  case False
  from False consider
      (neq) "n - length xs \<noteq> n - length ys" |
      (zero) "n - length xs = 0 \<and> n - length ys = 0"
    by linarith
  then show ?thesis
  proof (cases)
    case neq
    moreover have "count_list (pad n ys) (CHR ''_'') = n - length ys" using assms(2) count_pad by simp
    moreover have "count_list (pad n xs) (CHR ''_'') = n - length xs" using assms(1) count_pad by simp
    ultimately show ?thesis by metis
  next
    case zero
    thus ?thesis using False pad_def by auto
  qed
qed (simp add: pad_def assms(3))

lemma padl_neq:
  assumes "(CHR ''_'') \<notin> set xs" "CHR ''_'' \<notin> set ys" "xs \<noteq> ys"
  shows "padl n xs \<noteq> padl n ys"
proof (cases "length xs = length ys")
  case False
  from False consider
      (neq) "n - length xs \<noteq> n - length ys" |
      (zero) "n - length xs = 0 \<and> n - length ys = 0"
    by linarith
  then show ?thesis
  proof (cases)
    case neq
    moreover have "count_list (padl n ys) (CHR ''_'') = n - length ys" using assms(2) count_padl by simp
    moreover have "count_list (padl n xs) (CHR ''_'') = n - length xs" using assms(1) count_padl by simp
    ultimately show ?thesis by metis
  next
    case zero
    thus ?thesis using False padl_def by auto
  qed
qed (simp add: padl_def assms(3))

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


(* nat upto *)

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

lemma nat_upto_snoc: "nat_upto (Suc n) = nat_upto n @ [Suc n]"
  unfolding nat_upto_def
  apply simp using nat_upto_help_aux
  by (metis eq_Nil_appendI)


lemma nat_upto_prefix: "prefix (nat_upto n) (nat_upto (n+k))"
  apply (induction k)
   apply simp
  apply (subst add_Suc_right)
  apply (subst nat_upto_snoc)
  using prefix_def by auto

lemma nat_upto_distinct: "distinct (nat_upto n)"
proof -
  have "nat_upto n ! i \<noteq> nat_upto n ! j" if "i \<noteq> j" "i \<le> n" "j \<le> n" for i j
    using nat_upto_nth that by simp
  moreover have "i \<le> n \<longleftrightarrow> i < length (nat_upto n)" for i by auto
  ultimately show ?thesis using distinct_conv_nth by blast
qed

definition "unique_string (i::nat) \<equiv> show i"
definition "distinct_strings n \<equiv> map unique_string (case n of 0 \<Rightarrow> [] | Suc m \<Rightarrow> nat_upto m)"

(* TODO: https://isabelle.zulipchat.com/#narrow/channel/238552-Beginner-Questions/topic/String.20inequality.20with.20show/near/500270718*)
lemma show_nat_inj: fixes a :: nat and b :: nat assumes "a \<noteq> b" shows "show a \<noteq> show b"
  using assms sorry

(* TODO *)
lemma notin_show_nat: "CHR ''_'' \<notin> set (show (n::nat))" sorry

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

(* not sure how important those are *)

lemma distinct_strings_prefix: "prefix (distinct_strings n) (distinct_strings (n+k))"
  unfolding distinct_strings_def
  apply (simp split: nat.splits)
  using nat_upto_prefix map_mono_prefix by metis

lemma distinct_strings_padded:
  shows "distinct (map (pad k) (distinct_strings n))"
proof -
  let ?d = "distinct_strings n"
  {
    fix i j
    assume a: "i < length ?d" "j < length ?d" "i \<noteq> j"
    hence notin: "CHR ''_'' \<notin> set (?d ! i)" "CHR ''_'' \<notin> set (?d ! j)"
      using distinct_strings_def unique_string_def notin_show_nat list_ball_nth by simp_all
    from a have  "?d ! i \<noteq> ?d ! j" using distinct_strings_dist distinct_conv_nth by metis
    hence "pad k (?d ! i) \<noteq> pad k (?d ! j)" using pad_neq notin by simp
    hence "map (pad k) (distinct_strings n) ! i \<noteq> map (pad k) (distinct_strings n) ! j"
      using a by auto
  }
  thus ?thesis using distinct_conv_nth by force
qed

section \<open> useless, ahem, legacy stuff \<close>


definition distinctize :: "string list \<Rightarrow> string list \<Rightarrow> string list" where
  "distinctize blocked new \<equiv>
    map (append (safe_prefix blocked)) new"

(*lemma distinctize_correct:
  "disjnt (set blocked) (set (distinctize blocked new))"
  by (metis (no_types, opaque_lifting) disjnt_iff distinctize_def ex_map_conv safe_prefix_correct)*)


end