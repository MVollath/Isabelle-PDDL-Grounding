theory Tests
  imports Main
    (* "../LTS-formalization/Datalog/Datalog"
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    "Verified_SAT_Based_AI_Planning.STRIPS_Representation" *)
begin

text \<open>This is just a collection of random stuff. Read at your own risk.\<close>

value "{(True, True)}\<^sup>*"

lemma "(prod.swap ` s)\<^sup>* = prod.swap ` (s\<^sup>*)" oops
lemma "r\<inverse> = prod.swap ` r" by auto
lemma "(r\<inverse>)\<^sup>* = (r\<^sup>*)\<inverse>" by (rule rtrancl_converse)

locale el_localo =
  fixes types :: "(string \<times> string) list"

begin

definition "subtype_rel \<equiv> set (map prod.swap (types))"
definition of_type :: "string list \<Rightarrow> string list \<Rightarrow> bool" where
    "of_type oT T \<equiv> set oT \<subseteq> subtype_rel\<^sup>* `` set T"

value "(((\<lambda>x. None) :: int \<rightharpoonup> int set) (3 \<mapsto> {1, 2})) 3"
value "(((\<lambda>x. 2*x) :: int \<Rightarrow> int) (3 := 4))"
end

(* alternatively, use remdups on each bag at the end *)
fun conc_unique :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "conc_unique [] rs = rs" |
  "conc_unique (l # ls) rs = conc_unique ls (if l \<in> set rs then rs else l # rs)"

lemma conc_unique_set: "set (conc_unique xs ys) = set xs \<union> set ys"
  apply (induction xs arbitrary: ys)
  by auto
(*fun upd_bag :: "('a \<times> 'a list) \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> 'a list)" where
  "upd_bag (l, rs) R = R(l := conc_unique rs (R l))" *)

(* definition upd_bags :: "('a \<times> 'a list) list \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> 'a list)" where
  "upd_bags pairs R = fold upd_bag pairs R" *)

(* definition clomp where
  "clomp keys value \<equiv> map (\<lambda>k. (k, value)) keys" *)

(* definition shnu where
  "shnu rel r_ls l_rs \<equiv> upd_bags (clomp r_ls l_rs) rel" *)

definition upd_bag :: "'a list \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> 'a list)" where
  "upd_bag values key rel \<equiv> rel(key := conc_unique values (rel key))"

definition upd_all where
  "upd_all rel keys values \<equiv> fold (upd_bag values) keys rel"

thm upd_all_def[unfolded upd_bag_def]
lemma upd_all_cons:
  "upd_all rel (a#as) values = upd_all (rel(a := conc_unique values (rel a))) as values"
  by (simp add: upd_all_def[unfolded upd_bag_def])

(* This is going to be weird but bear with me *)

lemma
  assumes "rel k = v" "a \<noteq> k"
  shows "(rel (a := conc_unique values (rel a))) k = v"
  using assms by auto

lemma
  assumes "rel k = v"
  shows "set ((rel (k := conc_unique values (rel k))) k) = set values \<union> set (rel k)"
  using assms conc_unique_set by (metis fun_upd_same)

(* two properties we are interested in: that f k = the original value and that after the update with k=v, f k = {values} \<union> original
initially, f k = original. in each update step, if a=k, then result k = values + original.
otherwise, result = original.
*)

(* need some sort of inverse induction for this *)
lemma
  assumes "of_k_is_og y0"
    "\<forall>y. of_k_is_og y \<longrightarrow> of_k_is_un (f k y)"
    "\<forall>x y. of_k_is_un y \<longrightarrow> of_k_is_un (f x y)"
    "\<forall>x y. x \<noteq> k \<and> of_k_is_og y \<longrightarrow> of_k_is_og (f x y)"
    "k \<in> set xs"
  shows "of_k_is_un (fold f xs y0)"
  using assms
proof (induction xs arbitrary: y)
  case (Cons a as)
    show ?case
  proof (cases "k \<in> set as")
    case True
    note Cons.IH[OF assms(1) assms(2) assms(3) assms(4) this]
    hence "of_k_is_un (fold f as y0)" .
    oops

lemma fold_induct: "\<lbrakk>P y0; \<And>x y. P y \<Longrightarrow> P (f x y)\<rbrakk> \<Longrightarrow> P (fold f xs y0)"
  apply (induction xs arbitrary: y0)
  by simp_all

lemma todo: "\<forall>k. set (conc_unique values ((upd_all rel keys values) k)) = set values \<union> set (rel k)"
  oops



(* property is that applying conc_unique is like \<union>-ing values*)

lemma fold_upd_preserves:
  assumes "k \<notin> set keys"
  shows "fold (\<lambda>k f. f(k := v)) keys f k = f k"
  using assms
  by (induction keys arbitrary: f) simp_all

lemma
  assumes "k \<in> set ks"
  shows "fold (\<lambda>k f. f(k := v)) ks f k = v"
  using assms
proof (induction ks)
  case Nil thus ?case by simp
next
  case (Cons a as)
  have "fold (\<lambda>k f. f(k := v)) (a # as) f = fold (\<lambda>k f. f(k := v)) as (f(a := v))" by simp
  thus ?case
  proof (cases "k \<in> set as")
    case True
    then show ?thesis sorry
  next
    case False
    hence "fold (\<lambda>k f. f(k := v)) as f k = f k" using fold_upd_preserves by metis
    then show ?thesis sorry
  qed
qed

lemma
  assumes "k \<notin> set keys"
  shows "upd_all rel keys values k = rel k"
  using assms
proof (induction keys arbitrary: rel)
  case (Cons a as)
  hence "a \<noteq> k" using assms by auto
  thus ?case using upd_all_cons assms Cons
    by (metis fun_upd_idem_iff fun_upd_twist list.set_intros(2))
qed (simp add: upd_all_def)

  

lemma
  assumes "k \<in> set keys"
  shows "set (upd_all rel keys values k) = set (rel k) \<union> set values"
  using assms
proof (induction keys arbitrary: rel)
  case (Cons a as)
  have 1: "upd_all rel (a#as) values = upd_all (rel(a := conc_unique values (rel a))) as values"
    by (simp add: upd_all_cons)
  thus ?case
  proof (cases "a = k")
    case True
    hence "upd_all rel (a#as) values k = conc_unique values (rel a)" using 1 sorry
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed
qed simp


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

abbreviation reachable_nodes :: "('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> ('a list)" where
  "reachable_nodes rel \<equiv> reach_aux rel (\<lambda>x. [x]) (\<lambda>x. [x])"

value "map (reachable_nodes [(1::nat, 0::nat),(2,0),(3,2),(4,2),(5,4),(5,3),(7,3),(6,5)]) [0, 1, 2, 3, 4, 5, 6, 7]"
value "map (reachable_nodes ([(1, 0), (2, 0), (3, 1), (7, 6), (6, 5)]:: (nat\<times>nat) list)) [0, 1, 2, 3, 4, 5, 6, 7]"

lemma "(x, x) \<in> rel\<^sup>*" by simp

lemma reach_aux_aux: "reach_aux rel R L = reach_aux_aux rel dones R L"
  apply (induction rel arbitrary: dones R L)
  by auto

definition describes_rel :: "('a \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> bool" where
  "describes_rel rel bags \<equiv> \<forall>x y. y \<in> set (bags x) \<longleftrightarrow> (x, y) \<in> rel"

thm rtrancl_insert (* (insert (a, b) r)\<^sup>* = r\<^sup>* \<union> {(x, y). (x, a) \<in> r\<^sup>* \<and> (b, y) \<in> r\<^sup>*} *)



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

lemma "describes_rel ({}\<^sup>*) (\<lambda>x. [x])"
  by (auto simp add: describes_rel_def)
lemma "describes_rel (({}\<^sup>*)\<inverse>) (\<lambda>x. [x])"
  by (auto simp add: describes_rel_def)

lemma reach_aux_aux_usage:
  shows "describes_rel ((set rel)\<^sup>*) (reach_aux_aux rel [] (\<lambda>x. [x]) (\<lambda>x. [x]))"
proof -
  have 1: "describes_rel ((set [])\<^sup>*) (\<lambda>x. [x])" by (auto simp add: describes_rel_def)
  moreover have 2: "describes_rel (((set [])\<^sup>*)\<inverse>) (\<lambda>x. [x])" by (auto simp add: describes_rel_def)
  moreover note reach_aux_aux_correct[OF 1 2]
  ultimately show ?thesis by simp
qed


theorem reachable_iff_in_star: "describes_rel ((set rel)\<^sup>*) (reachable_nodes rel)"
  using reach_aux_aux_usage reach_aux_aux
  by metis



end