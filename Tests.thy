theory Tests
  imports Main
    (* "../LTS-formalization/Datalog/Datalog"
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    "Verified_SAT_Based_AI_Planning.STRIPS_Representation" *)
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Checker"
begin

lemma conj3: assumes "A \<and> B \<and> C" shows "A" "B" "C" using assms by simp_all

lemma conj2: assumes "A \<and> B" shows "A" "B" using assms by simp_all

lemma a: "(0::nat) < 3 \<and> (0::nat) < 6 \<and> (0::nat) < 9" sorry

thm conj3[OF a]

(* how hacky is this? *)
abbreviation uplus ("_ \<uplus> _ = _" 50) where
  "a \<uplus> b = x \<equiv> disjnt a b \<and> a \<union> b = x"



axiomatization f :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
  f_prop: "set (f rel) = (set rel)\<^sup>+"


datatype slorp = Slorp (ann : nat) (ben : nat)

fun gomp where "gomp (Slorp x y) = x + y"

thm slorp.collapse

lemma slorp_coll2: "\<lbrakk>\<And>x y. P (Slorp x y) x y\<rbrakk> \<Longrightarrow> P s (ann s) (ben s)"
  by (metis slorp.collapse)

lemma gomp2: "\<And>x y. gomp (Slorp x y) = x + y" by simp

thm slorp_coll2[where P = "\<lambda>s x y. gomp s = x + y", OF gomp2]


end