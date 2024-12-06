theory Graph_Funs
imports Main
begin

(* alternatively, use remdups on each bag at the end *)
fun conc_unique :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "conc_unique [] rs = rs" |
  "conc_unique (l # ls) rs = conc_unique ls (if l \<in> set rs then rs else l # rs)"

definition upd_bag :: "'a list \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> 'a list)" where
  "upd_bag values key rel \<equiv> rel(key := conc_unique values (rel key))"

definition upd_all where
  "upd_all rel keys values \<equiv> fold (upd_bag values) keys rel"

fun reach_aux :: "('a \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> ('a list)) \<Rightarrow> ('a \<Rightarrow> ('a list)) \<Rightarrow> ('a \<Rightarrow> ('a list))" where
  "reach_aux [] R L = L" |
  "reach_aux ((l, r) # rest) R L = 
    (let l_rs = R l; r_ls = L r in
    reach_aux rest
      (upd_all R r_ls l_rs)
      (upd_all L l_rs r_ls))"

fun reach_aux_aux :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> ('a list)) \<Rightarrow> ('a \<Rightarrow> ('a list)) \<Rightarrow> ('a \<Rightarrow> ('a list))" where
  "reach_aux_aux [] done R L = L" |
  "reach_aux_aux ((l, r) # todo) done R L = 
    (let l_rs = R l; r_ls = L r in
    reach_aux_aux todo ((l, r) # done)
      (upd_all R r_ls l_rs)
      (upd_all L l_rs r_ls))"

abbreviation reachable_nodes :: "('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "reachable_nodes rel \<equiv> reach_aux rel (\<lambda>x. [x]) (\<lambda>x. [x])"

(* the other functions were programmed before I understood the big problems with allowing constants
  to have "Either" types *)

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
    intersect_bags (reachable_nodes rel) all xs"

(* ---------------- PROOFS ------------------- *)

lemma conc_unique_un:
  "set (conc_unique xs ys) = set xs \<union> set ys"
  apply (induction xs arbitrary: ys)
  by auto

lemma group_bags_un:
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

lemma "\<Inter> ss = {s' | s'. \<forall>s \<in> ss. s' \<in> s}" by auto

lemma int_bags_int:
  "set (intersect_bags f all xs) = set all \<inter> \<Inter>{set (f x) | x. x \<in> set xs}"
proof (induction xs)
  case (Cons a as)
  have "set (intersect_bags f all (a#as)) =
    set (f a) \<inter> (set all \<inter> \<Inter>{set (f x) | x. x \<in> set as})"
    using Cons list_int_int intersect_bags.simps(2) by metis
  thus ?case by auto
qed simp

lemma upd_all_cons:
  "upd_all rel (a#as) values = upd_all (rel(a := conc_unique values (rel a))) as values"
  by (simp add: upd_all_def[unfolded upd_bag_def])

abbreviation describes_rel :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> bool" where
  "describes_rel rel bags \<equiv> \<forall>x y. y \<in> set (bags x) \<longleftrightarrow> (x, y) \<in> rel"

(* TODO use this *)
lemma "foldr f xs i = fold f (rev xs) i"
  by (metis foldr_conv_fold)

lemma upd_all_L:
  assumes "describes_rel (rel\<^sup>*) L"
          "describes_rel ((rel\<^sup>*)\<inverse>) R"
  shows "describes_rel (({(l, r)} \<union> rel)\<^sup>*) (upd_all L (R l) (L r))"
  sorry

lemma upd_all_R:
  assumes "describes_rel (rel\<^sup>*) L"
          "describes_rel ((rel\<^sup>*)\<inverse>) R"
        shows "describes_rel ((({(l, r)} \<union> rel)\<^sup>*)\<inverse>) (upd_all R (L r) (R l))"
proof -
  from assms(2) have 1: "describes_rel ((rel\<inverse>)\<^sup>*) R" by (simp add: rtrancl_converse)
  from assms(1) have 2: "describes_rel (((rel\<inverse>)\<^sup>*)\<inverse>) L" by (simp add: rtrancl_converse)
  have 3: "describes_rel (({(r, l)} \<union> rel\<inverse>)\<^sup>*) (upd_all R (L r) (R l))"
    by (rule upd_all_L[OF 1 2])
  have "({(l, r)} \<union> rel)\<inverse> = {(r, l)} \<union> rel\<inverse>" by auto
  moreover have   "(({(l, r)} \<union> rel)\<^sup>*)\<inverse> = (({(l, r)} \<union> rel)\<inverse>)\<^sup>*" by (simp add: rtrancl_converse)
  ultimately have "(({(l, r)} \<union> rel)\<^sup>*)\<inverse> = ({(r, l)} \<union> rel\<inverse>)\<^sup>*" by simp
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



theorem reachable_iff_in_star: "describes_rel ((set rel)\<^sup>*) (reachable_nodes rel)"
  using reach_aux_aux_usage reach_aux_aux
  by metis

lemma reachable_iff_any_in_star:
  "y \<in> set (reachable_nodes_froms rel xs) \<longleftrightarrow>
    (\<exists>x \<in> set xs. (x, y) \<in> (set rel)\<^sup>*)"
proof -
  have "y \<in> set (reachable_nodes_froms rel xs) \<longleftrightarrow>
    y \<in> \<Union>{set ((reachable_nodes rel) x) | x. x \<in> set xs}" using group_bags_un by metis
  also have "... \<longleftrightarrow> (\<exists>x \<in> set xs. y \<in> set ((reachable_nodes rel) x))" by auto
  finally show ?thesis using reachable_iff_in_star by metis
qed

lemma reachable_iff_all_in_star:
  "y \<in> set (common_reachable_nodes rel all xs) \<longleftrightarrow>
    y \<in> set all \<and> (\<forall>x \<in> set xs. (x, y) \<in> (set rel)\<^sup>*)"
proof -
  have "y \<in> set (common_reachable_nodes rel all xs) \<longleftrightarrow>
    y \<in> set all \<inter> \<Inter>{set ((reachable_nodes rel) x) | x. x \<in> set xs}" using int_bags_int by metis
  also have "... \<longleftrightarrow> y \<in> set all \<and> (\<forall>x \<in> set xs. y \<in> set ((reachable_nodes rel) x))" by auto
  finally show ?thesis using reachable_iff_in_star by metis
qed


end