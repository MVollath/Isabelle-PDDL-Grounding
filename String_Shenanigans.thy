theory String_Shenanigans
imports Main "Show.Show_Instances" "HOL-Library.Sublist"
begin

abbreviation max_length :: "'a list list \<Rightarrow> nat" where
  "max_length xss \<equiv> Max (length ` set xss)"

definition safe_prefix :: "string list \<Rightarrow> string" where
  "safe_prefix ss \<equiv> replicate (max_length ss + 1) (CHR ''_'')"

lemma safe_prefix_correct: "safe_prefix xs @ x \<notin> set xs"
proof -
  have "\<forall>s \<in> set ss. length s \<le> max_length ss" for ss :: "string list"
    by simp
  thus ?thesis using safe_prefix_def by fastforce
qed

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
  have "\<forall>s \<in> set ss. length s \<le> max_length ss"
    by simp
  moreover have "max_length ss + 1 \<le> length (make_unique ss x)"
    using make_unique_def pad_length(2) by simp
  ultimately have "\<forall>s \<in> set ss. length s < length (make_unique ss x)"
    by (meson add_le_mono1 le_trans less_iff_succ_less_eq)
  thus ?thesis by auto
qed


definition pad_strings :: "string list \<Rightarrow> string list" where
  "pad_strings ss \<equiv> map (pad (max_length ss + 1)) ss"


(* nat upto *)

fun nat_range_help :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "nat_range_help 0 build = build" |
  "nat_range_help (Suc n) build = nat_range_help n (n # build)"

definition "nat_range n \<equiv> nat_range_help n []"

lemma nat_range_help_len: "length (nat_range_help n xs) = n + length xs"
  by (induction n arbitrary: xs) simp_all

lemma nat_range_length [simp]: "length (nat_range n) = n"
  using nat_range_def nat_range_help_len by simp

lemma nat_range_help_aux: "nat_range_help n (xs @ ys) = nat_range_help n xs @ ys"
  by (induction n xs rule: nat_range_help.induct) simp_all

lemma nat_range_help_nth: assumes "i < n" shows "nat_range_help n xs ! i = i"
  using assms proof (induction n xs rule: nat_range_help.induct)
  case (2 n xs)
  then consider "i < n" | (eq) "i = n" by linarith
  thus ?case proof (cases)
    case eq
    have "nat_range_help (Suc n) xs = nat_range_help n ([] @ (n # xs))"
      by simp
    also have "... = nat_range_help n [] @ (n # xs)"
      using nat_range_help_aux by metis
    also have "i = length (nat_range_help n [])"
      using nat_range_help_len eq by simp
    ultimately show ?thesis using eq
      by (metis nth_append_length)
  qed (simp add: 2)
qed simp_all

lemma nat_range_nth [simp]: assumes "i < n" shows "nat_range n ! i = i"
  using assms nat_range_help_nth nat_range_def by simp

lemma nat_range_zero[simp]: "nat_range 0 = []"
  unfolding nat_range_def by simp

lemma nat_range_snoc[simp]: "nat_range (Suc n) = nat_range n @ [n]"
  unfolding nat_range_def nat_range_help.simps
  using nat_range_help_aux by (metis eq_Nil_appendI)

lemmas nat_range_simps = nat_range_zero nat_range_snoc

lemma nat_range_prefix: "prefix (nat_range n) (nat_range (n+k))"
  apply (induction k)
   apply simp
  apply (subst add_Suc_right)
  apply (subst nat_range_snoc)
  using prefix_def by auto

lemma nat_range_dist: "distinct (nat_range n)"
proof -
  have "nat_range n ! i \<noteq> nat_range n ! j" if "i \<noteq> j" "i < n" "j < n" for i j
    using nat_range_nth that by simp
  moreover have "i < n \<longleftrightarrow> i < length (nat_range n)" for i by auto
  ultimately show ?thesis using distinct_conv_nth by blast
qed

definition "distinct_strings n \<equiv> map show (nat_range n)"

(* TODO: https://isabelle.zulipchat.com/#narrow/channel/238552-Beginner-Questions/topic/String.20inequality.20with.20show/near/500270718*)
lemma show_nat_inj: fixes a :: nat and b :: nat assumes "a \<noteq> b" shows "show a \<noteq> show b"
  using assms sorry

(* TODO *)
lemma notin_show_nat: "CHR ''_'' \<notin> set (show (n::nat))" sorry

lemma nat_show_len_mono: "i \<le> j \<Longrightarrow> length (show i) \<le> length (show j)"
  sorry




lemma unique_str_bij:
  fixes i :: nat and j :: nat
  shows "i \<noteq> j \<longleftrightarrow> show i \<noteq> show j"
  using show_nat_inj by auto

lemma distinct_str_length [simp]: "length (distinct_strings n) = n"
  unfolding distinct_strings_def
  by (cases n) simp_all

lemma distinct_strings_nth [simp]:
  assumes "i < n" shows "distinct_strings n ! i = show i"
  unfolding distinct_strings_def using assms
  by (metis nat_range_length nat_range_nth nth_map)

lemma distinct_strings_dist:
  "distinct (distinct_strings n)"
  using unique_str_bij distinct_conv_nth by fastforce

(* not sure how important those are *)

lemma distinct_strings_max_len:
  assumes "m \<le> n"
  shows "\<forall>x \<in> set (distinct_strings m). length x \<le> length (show n)"
  unfolding distinct_strings_def
using assms proof (induction n arbitrary: m)
  case (Suc n)
  have "set (distinct_strings (Suc n)) = insert (show n) (set (distinct_strings n))"
    unfolding distinct_strings_def nat_range_simps by force
  moreover have "length (show n) \<le> length (show (Suc n))"
    using nat_show_len_mono
    by (metis Suc_n_not_le_n nat_le_linear)
  ultimately show ?case using Suc (* TODO simplify *)
    by (metis (mono_tags, lifting) Suc_le_mono distinct_strings_def dual_order.trans insertE le_SucE)
qed simp

lemma distinct_strings_prefix: "prefix (distinct_strings n) (distinct_strings (n+k))"
  using distinct_strings_def nat_range_prefix map_mono_prefix by metis

lemma pad_show_neq:
  fixes i j :: nat
  assumes "i \<noteq> j"
  shows "padl k (show i) \<noteq> padl k (show j)"
  using assms padl_neq notin_show_nat show_nat_inj by simp

(* TODO pull inner if i neq j out to generalize for when map isn't explicitly used *)
lemma distinct_strings_padded:
  shows "distinct (map (padl k) (distinct_strings n))"
proof -
  let ?d = "distinct_strings n"
  have "map (padl k) ?d ! i \<noteq> map (padl k) ?d ! j"
    if "i < length ?d" "j < length ?d" "i \<noteq> j" for i j
    using that distinct_strings_dist distinct_conv_nth list_ball_nth
  proof -
    (* TODO simplify with pad_show_neq *)
    from that have notin: "CHR ''_'' \<notin> set (?d ! i)" "CHR ''_'' \<notin> set (?d ! j)"
      using distinct_strings_def notin_show_nat list_ball_nth by simp_all
    from that have  "?d ! i \<noteq> ?d ! j" using distinct_strings_dist distinct_conv_nth by metis
    hence "padl k (?d ! i) \<noteq> padl k (?d ! j)" using padl_neq notin by simp
    thus ?thesis using that by auto
  qed
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