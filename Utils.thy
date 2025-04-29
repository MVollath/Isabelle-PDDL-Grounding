theory Utils
  imports Main
begin

(* for testing *)
definition
  "showvals f xs \<equiv> map (\<lambda>x. (x, f x)) xs"

fun showsteps :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list" where
  "showsteps f i [] = [i]" |
  "showsteps f i (x # xs) = i # showsteps f (f i x) xs"

(* syntax sugar *)


text \<open> Not using the default list_all because it makes proofs cumbersome \<close>
abbreviation (input) list_all1 where
  "list_all1 P xs \<equiv> \<forall>x \<in> set xs. P x"

(* rule rewriting *)

lemma conj_split_4:
  assumes "A \<and> B \<and> C \<and> D"
  shows "A" "B" "C" "D"
  using assms by simp_all

lemma conj_split_5:
  assumes "A \<and> B \<and> C \<and> D \<and> E"
  shows "A" "B" "C" "D" "E"
  using assms by simp_all

lemma conj_split_7:
  assumes "A \<and> B \<and> C \<and> D \<and> E \<and> F \<and> G"
  shows "A" "B" "C" "D" "E" "F" "G"
  using assms by simp_all

(* proof rules *)

lemma eq_contr: "(a = b \<Longrightarrow> False) \<Longrightarrow> a \<noteq> b"
  by auto

(* lists *)

(* Saves a a line or two sometimes *)
lemma list_induct_n [case_names nil suc]:
  assumes "length xs = n" "P [] 0"
  "\<And>x xs n. length xs = n \<Longrightarrow>
  P xs n \<Longrightarrow> P (x # xs) (Suc n)" shows "P xs n"
using assms proof (induction xs arbitrary: n)
  case (Cons x xs n)
  thus ?case by (cases n) simp_all
qed simp

fun sublist_until :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "sublist_until [] a = []" |
  "sublist_until (x # xs) a =
    (if x = a then [] else x # sublist_until xs a)"

lemma sublist_just_until:
  assumes "x \<in> set xs"
  shows "\<exists>ys. sublist_until xs x @ [x] @ ys = xs"
  using assms by (induction xs) auto

lemma notin_sublist_until:
  "x \<notin> set (sublist_until xs x)"
  by (induction xs) simp_all

(* map *)

lemma map_of_in_R_iff: "x \<in> fst ` set m \<longleftrightarrow> (\<exists>y. map_of m x = Some y)"
  by (metis map_of_eq_None_iff not_None_eq)

lemma map_of_single_val:
  assumes "\<forall>(x, y) \<in> set m. y = z"
  shows "x \<in> fst ` set m \<longleftrightarrow> map_of m x = Some z"
  using assms map_of_in_R_iff
  by (metis (full_types) case_prodD map_of_SomeD)

(* TODO just use distinct_map *)
lemma map_inj_dis:
  assumes "distinct xs" "inj f"
  shows "distinct (map f xs)"
  using assms distinct_map subset_inj_on by blast

lemma map_set_comprehension:
  "{f (xs ! i) | i. i < length xs} = set (map f xs)"
proof -
  have "{f (xs ! i) | i. i < length xs} = {f x | x. x \<in> set xs}"
    by (metis in_set_conv_nth)
  thus ?thesis by auto
qed

lemma append_r_distinct: "distinct xs \<Longrightarrow> distinct (map (\<lambda>x. x @ p) xs)" (is "?L \<Longrightarrow> ?R")
proof - (* TODO how to apply contradiction correctly here? *)
  assume l: ?L
  {assume "\<not>?R"
    then obtain i j where
      ij: "i < length xs" "j < length xs" "i \<noteq> j"
      "map (\<lambda>x. x @ p) xs ! i = map (\<lambda>x. x @ p) xs ! j"
      by (metis distinct_conv_nth length_map)
    hence "xs ! i = xs ! j" by simp
    hence "\<not>?L" using ij distinct_conv_nth by blast}
  thus ?thesis using l by auto
qed

lemma append_l_distinct: "distinct xs \<Longrightarrow> distinct (map ((@)p) xs)" (is "?L \<Longrightarrow> ?R")
proof - (* TODO how to apply contradiction correctly here? *)
  assume l: ?L
  {assume "\<not>?R"
    then obtain i j where
      ij: "i < length xs" "j < length xs" "i \<noteq> j"
      "map ((@)p) xs ! i = map ((@)p) xs ! j"
      by (metis distinct_conv_nth length_map)
    hence "xs ! i = xs ! j" by simp    
    hence "\<not>?L" using ij distinct_conv_nth by blast}
  thus ?thesis using l by auto
qed

(* map2 *)

lemma map2_obtain:
  assumes "z \<in> set (map2 f xs ys)"
  obtains x y where "z = f x y" "x \<in> set xs" "y \<in> set ys"
  using assms by (induction xs ys rule: list_induct2') auto

(* TODO, if I end up using it *)
lemma map2_dist_2:
  assumes "distinct ys" "\<And>x1 x2 y1 y2. y1 \<in> set ys \<Longrightarrow> y2 \<in> set ys \<Longrightarrow> y1 \<noteq> y2 \<Longrightarrow> f x1 y1 \<noteq> f x2 y2"
  shows "distinct (map2 f xs ys)"
  using assms proof (induction xs ys rule: list_induct2')
  case (4 x xs y ys)
  hence "distinct (map2 f xs ys)" by simp

  thus ?case apply (induction xs ys rule: list_induct2') oops


lemma drop_prefix:
  assumes "length xs = n" shows "drop n (xs @ ys) = ys"
  by (induction rule: list_induct_n[OF assms]) simp_all

lemma "length xs = length ys \<Longrightarrow> distinct ys \<Longrightarrow> inj_on (map_of (zip xs ys)) (set xs)"
  oops


end