theory Graph_Funs
imports Main
begin

(* alternatively, use remdups on each bag at the end *)
text \<open> the use of conc_unique here is only for performance issues and I probably should
not have bothered with it.\<close>
fun conc_unique :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "conc_unique [] rs = rs" |
  "conc_unique (l # ls) rs = conc_unique ls (if l \<in> set rs then rs else l # rs)"

definition upd_bag :: "'a list \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> 'a list)" where
  "upd_bag values key rel \<equiv> rel(key := conc_unique values (rel key))"

definition upd_all where
  "upd_all rel keys values \<equiv> foldr (upd_bag values) keys rel"
(*foldr is easier to prove by induction *)

fun reach_aux :: "('a \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> ('a list)) \<Rightarrow> ('a \<Rightarrow> ('a list)) \<Rightarrow> ('a \<Rightarrow> ('a list))" where
  "reach_aux [] R L = L" |
  "reach_aux ((l, r) # rest) R L = 
    (let l_rs = R l; r_ls = L r in
    reach_aux rest
      (upd_all R r_ls l_rs)
      (upd_all L l_rs r_ls))"

(* only used in proofs *)
fun reach_aux_aux :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> ('a list)) \<Rightarrow> ('a \<Rightarrow> ('a list)) \<Rightarrow> ('a \<Rightarrow> ('a list))" where
  "reach_aux_aux [] done R L = L" |
  "reach_aux_aux ((l, r) # todo) done R L = 
    (let l_rs = R l; r_ls = L r in
    reach_aux_aux todo ((l, r) # done)
      (upd_all R r_ls l_rs)
      (upd_all L l_rs r_ls))"

text \<open> TODO: use mapping instead of lambda! \<close>
abbreviation reachable_nodes :: "('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "reachable_nodes rel \<equiv> reach_aux rel (\<lambda>x. [x]) (\<lambda>x. [x])"

(* the following (unused) functions were programmed before I understood the big problems with allowing constants
  to have "Either" types *)
(*
fun group_bags :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "group_bags f [] = []" |
  "group_bags f (x # xs) = conc_unique (f x) (group_bags f xs)"
  
abbreviation reachable_nodes_froms :: "('a \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "reachable_nodes_froms rel xs \<equiv> group_bags (reachable_nodes rel) xs"

abbreviation list_int :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_int xs ys \<equiv> filter (\<lambda>y. y \<in> set xs) ys"

(* "all" is the universe, it represents the coset of []. *)
fun intersect_bags :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'b list \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "intersect_bags f all [] = all" |
  "intersect_bags f all (x # xs) = list_int (f x) (intersect_bags f all xs)"

abbreviation common_reachable_nodes :: "('a \<times> 'a) list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "common_reachable_nodes rel all xs \<equiv>
    intersect_bags (reachable_nodes rel) all xs"*)

(* ---------------- PROOFS ------------------- *)

lemma conc_unique_un:
  "set (conc_unique xs ys) = set xs \<union> set ys"
  apply (induction xs arbitrary: ys)
  by auto

(*lemma group_bags_un:
  "set (group_bags f xs) = \<Union>{set (f x) | x. x \<in> set xs}"
proof (induction xs)
  case (Cons a as)
  have "set (group_bags f (a#as)) = set (conc_unique (f a) (group_bags f as))"
    by simp
  also have "... = set (f a) \<union> \<Union>{set (f x) | x. x \<in> set as}" using Cons conc_unique_un by metis
  finally show ?case by auto
qed simp

lemma list_int_int:
  "set (list_int xs ys) = set xs \<inter> set ys" by auto

lemma int_bags_int:
  "set (intersect_bags f all xs) = set all \<inter> \<Inter>{set (f x) | x. x \<in> set xs}"
proof (induction xs)
  case (Cons a as)
  have "set (intersect_bags f all (a#as)) =
    set (f a) \<inter> (set all \<inter> \<Inter>{set (f x) | x. x \<in> set as})"
    using Cons list_int_int intersect_bags.simps(2) by metis
  thus ?case by auto
qed simp *)


definition describes_rel :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> bool" where
  "describes_rel rel bags \<equiv> \<forall>x y. y \<in> set (bags x) \<longleftrightarrow> (x, y) \<in> rel"
declare describes_rel_def[simp]

lemma desc_rel_alt: "describes_rel rel bags \<longleftrightarrow> (\<forall>x. set (bags x) = {y. (x, y) \<in> rel})"
  by auto

lemma "describes_rel r f \<Longrightarrow> describes_rel (insert (a, b) r) (f(a:=b # f a))"
  by simp

value "Pair False True"

lemma "{(a, b) | b. b \<in> bs} = (Pair a) ` bs" by auto

lemma upd_bag_aux:
  assumes "set u = vs \<union> set (f x)"
    "describes_rel r f"
  shows "describes_rel (r \<union> (Pair x) ` vs) (f(x:=u))"
  using assms by auto

lemma upd_bag_correct:
  "describes_rel r f \<Longrightarrow> describes_rel (r \<union> (Pair x) ` set vals) (upd_bag vals x f)"
  using conc_unique_un upd_bag_aux upd_bag_def by metis


definition upd_all2 where
  "upd_all2 r keys vals = fold (upd_bag vals) keys r"

lemma "upd_all r (k#ks) vs = upd_bag vs k (upd_all r ks vs)"
  unfolding upd_all_def by simp

lemma "upd_all2 r (k#ks) vs = upd_all2 (upd_bag vs k r) ks vs"
  unfolding upd_all2_def by simp

lemma "Pair x ` vs = {(x, v)|v. v \<in> vs}" by auto

lemma upd_all_correct:
  assumes "describes_rel r f"
  shows "describes_rel (r \<union> {(k, v). k \<in> set ks \<and> v \<in> set vs}) (upd_all f ks vs)"
  using assms
proof (induction ks)
  case Nil
  thus ?case unfolding upd_all_def by simp
next
  case Cons
  note Cons.IH[OF Cons.prems]
  note upd_bag_correct[OF this]
  thus ?case unfolding upd_all_def by auto
qed

(* TODO use this *)
lemma "foldr f xs i = fold f (rev xs) i"
  by (metis foldr_conv_fold)

thm rtrancl_insert

lemma rtrancl_insert_elem: "(a, b) \<in> (insert (c, d) rel)\<^sup>* \<longleftrightarrow>
        (a, b) \<in> rel\<^sup>* \<or> ((a, c) \<in> rel\<^sup>* \<and> (d, b) \<in> rel\<^sup>*)"
  using rtrancl_insert (* by fast: 4 seconds *)
proof -
  have "(a, b) \<in> (insert (c, d) rel)\<^sup>* \<longleftrightarrow>
    (a, b) \<in> rel\<^sup>* \<union> {(x, y). (x, c) \<in> rel\<^sup>* \<and> (d, y) \<in> rel\<^sup>*}"
    using rtrancl_insert by metis
  thus ?thesis by simp
qed

lemma upd_all_L:
  assumes "describes_rel (rel\<^sup>*) L"
          "describes_rel ((rel\<^sup>*)\<inverse>) R"
  shows "describes_rel ((insert (l, r) rel)\<^sup>*) (upd_all L (R l) (L r))"
proof -
  let ?B = "upd_all L (R l) (L r)"
  have "describes_rel (rel\<^sup>* \<union> {(k, v). k \<in> set (R l) \<and> v \<in> set (L r)}) ?B"
    using upd_all_correct[OF assms(1)] .
  hence "describes_rel (rel\<^sup>* \<union> {(k, v). (l, k) \<in> (rel\<^sup>*)\<inverse> \<and> (r, v) \<in> rel\<^sup>*}) ?B"
    using assms by simp
  hence "describes_rel (rel\<^sup>* \<union> {(k, v). (k, l) \<in> rel\<^sup>* \<and> (r, v) \<in> rel\<^sup>*}) ?B" by simp
  thus ?thesis using assms rtrancl_insert by metis
qed

lemma upd_all_R:
  assumes "describes_rel (rel\<^sup>*) L"
          "describes_rel ((rel\<^sup>*)\<inverse>) R"
        shows "describes_rel (((insert (l, r) rel)\<^sup>*)\<inverse>) (upd_all R (L r) (R l))"
proof -
  from assms(2) have 1: "describes_rel ((rel\<inverse>)\<^sup>*) R" by (simp add: rtrancl_converse)
  from assms(1) have 2: "describes_rel (((rel\<inverse>)\<^sup>*)\<inverse>) L" by (simp add: rtrancl_converse)
  have 3: "describes_rel ((insert (r, l) (rel\<inverse>))\<^sup>*) (upd_all R (L r) (R l))"
    by (rule upd_all_L[OF 1 2])
  have "(insert (l, r) rel)\<inverse> = insert (r, l) (rel\<inverse>)" by auto
  moreover have   "((insert (l, r) rel)\<^sup>*)\<inverse> = ((insert (l, r) rel)\<inverse>)\<^sup>*" by (simp add: rtrancl_converse)
  ultimately have "((insert (l, r) rel)\<^sup>*)\<inverse> = (insert (r, l) (rel\<inverse>))\<^sup>*" by simp
  from 3 this show ?thesis by simp
qed

lemma reach_aux_aux: "reach_aux rel R L = reach_aux_aux rel dones R L"
  apply (induction rel arbitrary: dones R L)
  by auto

lemma reach_aux_aux_correct:
  assumes "describes_rel ((set dones)\<^sup>*) L"
          "describes_rel (((set dones)\<^sup>*)\<inverse>) R"
  shows "describes_rel ((set todo \<union> set dones)\<^sup>*) (reach_aux_aux todo dones R L)"
  using assms
proof (induction todo arbitrary: dones L R)
  case (Cons t todo)
  let ?rel = "set dones"
  obtain l r where lr: "t = (l, r)" by fastforce
  note reach_aux_aux.simps(2)[unfolded Let_def] (* TODO how to have simp deal with "let" again? *)
  hence aux_it: "reach_aux_aux ((l, r) # todo) dones R L =
    reach_aux_aux todo ((l, r) # dones)
      (upd_all R (L r) (R l))
      (upd_all L (R l) (L r))" by simp
  
  have L: "describes_rel ((set ((l, r) # dones))\<^sup>*) (upd_all L (R l) (L r))"
    using assms Cons.prems upd_all_L by simp
  have R: "describes_rel (((set ((l, r) # dones))\<^sup>*)\<inverse>) (upd_all R (L r) (R l))"
    using assms Cons.prems upd_all_R by simp
  from L R have "describes_rel ((set todo \<union> set ((l, r) # dones))\<^sup>*)
   (reach_aux_aux todo ((l, r) # dones) (upd_all R (L r) (R l)) (upd_all L (R l) (L r)))"
    by (rule Cons.IH)
  hence "describes_rel ((set (t # todo) \<union> set dones)\<^sup>*)
    (reach_aux_aux (t # todo) dones R L)" using aux_it lr by simp
  thus ?case .
qed simp

lemma reach_aux_aux_usage:
  shows "describes_rel ((set rel)\<^sup>*) (reach_aux_aux rel [] (\<lambda>x. [x]) (\<lambda>x. [x]))"
proof -
  have 1: "describes_rel ((set [])\<^sup>*) (\<lambda>x. [x])" by auto
  moreover have 2: "describes_rel (((set [])\<^sup>*)\<inverse>) (\<lambda>x. [x])" by auto
  moreover note reach_aux_aux_correct[OF 1 2]
  ultimately show ?thesis by simp
qed

declare describes_rel_def[simp del]

(* \<longleftrightarrow> "describes_rel ((set rel)\<^sup>* ) (reachable_nodes rel)" *)
theorem reachable_iff_in_star: "y \<in> set (reachable_nodes rel x) \<longleftrightarrow> (x, y) \<in> (set rel)\<^sup>*"
  using reach_aux_aux_usage reach_aux_aux describes_rel_def
  by metis

lemma reachable_set: "set (reachable_nodes rel x) \<subseteq> insert x (snd ` set rel)"
proof -
  have "set (reachable_nodes rel x) = {y. (x, y) \<in> (set rel)\<^sup>*}"
    using reachable_iff_in_star by fast
  also have "... = (set rel)\<^sup>* `` {x}" by auto
  also have "... = insert x ((set rel)\<^sup>+ `` {x})" using rtrancl_trancl_reflcl by blast
  also have "... \<subseteq> insert x (snd ` (set rel)\<^sup>+)" by force
  also have "... = insert x (snd ` set rel)" by (metis trancl_range snd_eq_Range)
  finally show ?thesis .
qed

(* artifact from when I misunderstood Either types *)
(*
lemma reachable_iff_any_in_star:
  "y \<in> set (reachable_nodes_froms rel xs) \<longleftrightarrow>
    (\<exists>x \<in> set xs. (x, y) \<in> (set rel)\<^sup>* )"
proof -
  have "y \<in> set (reachable_nodes_froms rel xs) \<longleftrightarrow>
    y \<in> \<Union>{set ((reachable_nodes rel) x) | x. x \<in> set xs}" using group_bags_un by metis
  also have "... \<longleftrightarrow> (\<exists>x \<in> set xs. y \<in> set ((reachable_nodes rel) x))" by auto
  finally show ?thesis using reachable_iff_in_star by metis
qed

(* artifact from when I misunderstood Either types *)
lemma reachable_iff_all_in_star:
  "y \<in> set (common_reachable_nodes rel all xs) \<longleftrightarrow>
    y \<in> set all \<and> (\<forall>x \<in> set xs. (x, y) \<in> (set rel)\<^sup>* )"
proof -
  have "y \<in> set (common_reachable_nodes rel all xs) \<longleftrightarrow>
    y \<in> set all \<inter> \<Inter>{set ((reachable_nodes rel) x) | x. x \<in> set xs}" using int_bags_int by metis
  also have "... \<longleftrightarrow> y \<in> set all \<and> (\<forall>x \<in> set xs. y \<in> set ((reachable_nodes rel) x))" by auto
  finally show ?thesis using reachable_iff_in_star by metis
qed *)

(* if I fail to prove this, I can always use remdups as a crutch *)
lemma reachable_dis: "distinct (reachable_nodes rel x)" sorry



end