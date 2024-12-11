theory Tests
  imports Main
    (* "../LTS-formalization/Datalog/Datalog"
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    "Verified_SAT_Based_AI_Planning.STRIPS_Representation" *)
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Checker"
begin

text \<open>This is just a collection of random stuff. Read at your own risk.\<close>

subsection \<open> locale/context tutorial \<close>
locale my_loc =
  fixes x :: int
begin

definition "evsa \<equiv> even x"

end

interpretation ahsh: my_loc 6 .

value "ahsh.evsa"


context my_loc
begin

definition "cool \<equiv> x - 1"

context
  fixes scale :: int
begin
definition "sc_x \<equiv> scale * x"

end

end

value "ahsh.cool"
value "ahsh.sc_x 6"

locale my_loc2 = my_loc +
  assumes ev: evsa
begin

definition "hot \<equiv> x + 1"
end

interpretation lava : my_loc2 4
  by (simp add: my_loc.evsa_def my_loc2_def)


print_locale! my_loc2
thm my_loc2_def

definition (in my_loc2) "sixer \<equiv> x+6"
lemma (in my_loc2) sixer_even: "even sixer"
  using ev evsa_def sixer_def by auto

thm "lava.sixer_even"
thm "my_loc2.sixer_even"

value "lava.sixer"

locale my_loc3 = my_loc2 "fst pair" for
  pair :: "int \<times> int" +
  assumes pair_eq: "fst pair = snd pair"

locale my_loc_dos =
  un: my_loc2 a + dos: my_loc2 b
  for a and b +
  assumes pair_eq: "a = b"
begin

lemma "(a + b) mod 4 = 0"
proof -
  have "even a"
    using un.ev un.evsa_def by auto
  oops

lemma "un.evsa" by (simp add: un.ev)

end

(* sublocale, but I'm too lazy for an example rn *)

(* unique existence *)

definition "g \<equiv> THE x. x = (5::nat) + 1"
thm ex1_eq
lemma "\<exists>! h. (5::nat) + 1 = h" sorry

lemma "\<exists>h. P h \<Longrightarrow> \<forall>a b. P a \<and> P b \<longrightarrow> a = b \<Longrightarrow> \<exists>!h. P h"
  by blast

definition "d \<equiv> THE x. x > (5::nat)"

lemma "y = (THE x. P x) \<Longrightarrow> \<exists>!x. P x" oops

(* random *)

definition foo :: "nat \<Rightarrow> [nat, nat] \<Rightarrow> nat" where
  "foo a b c = a + b - c"



end