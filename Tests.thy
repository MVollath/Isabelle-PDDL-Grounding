theory Tests
  imports Main
    (* "../LTS-formalization/Datalog/Datalog"
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    "Verified_SAT_Based_AI_Planning.STRIPS_Representation"
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Checker" *)
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    "HOL-Library.Monad_Syntax"
    "HOL-Library.Multiset"
begin

term "count"

datatype ('a, 'e) Err = Lef 'a | Rig 'e

type_synonym ('a, 'e) err_ = "('a, 'e) Err" (infixl "#" 0)

fun bind :: "('a # 'e) \<Rightarrow> ('a \<Rightarrow> ('b # 'e)) \<Rightarrow> ('b # 'e)" where
  "bind (Lef x) f = f x"|
  "bind (Rig e) f = Rig e"

adhoc_overloading
  Monad_Syntax.bind bind

definition "dub x = Lef (x + x)"
definition "odub x = Some (x + x)"

value "(Rig False :: nat # bool) \<bind> dub"
value "(None :: nat option) \<bind> odub"

lemma "{x. \<exists>B \<in> s. x \<in> B} = \<Union>s" by auto
lemma fixes a :: "'a set" shows "a \<bind> f = \<Union>(f ` a)"
  by (rule Complete_Lattices.bind_UNION)

(* ------------------------------------------------------------------------------------ *)

lemma conj3: assumes "A \<and> B \<and> C" shows "A" "B" "C" using assms by simp_all

lemma conj2: assumes "A \<and> B" shows "A" "B" using assms by simp_all

lemma a: "(0::nat) < 3 \<and> (0::nat) < 6 \<and> (0::nat) < 9" by simp

thm conj3[OF a]




axiomatization f :: "('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
  f_prop: "set (f rel) = (set rel)\<^sup>+"


datatype slorp = Slorp (ann : nat) (ben : nat)

fun gomp where "gomp (Slorp x y) = x + y"

thm slorp.collapse

lemma slorp_coll2: "\<lbrakk>\<And>x y. P (Slorp x y) x y\<rbrakk> \<Longrightarrow> P s (ann s) (ben s)"
  by (metis slorp.collapse)

lemma gomp2: "\<And>x y. gomp (Slorp x y) = x + y" by simp

thm slorp_coll2[where P = "\<lambda>s x y. gomp s = x + y", OF gomp2]

datatype 'a foom = Aned 'a 'a | Batt "'a list"

value "map_foom (\<lambda>x :: nat. True)"



end