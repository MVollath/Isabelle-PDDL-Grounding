theory Testing_Hacks
  imports Main
begin

datatype ('a) result = Correctly 'a | Incorrectly 'a

definition assert_eq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a result" where
  "assert_eq v1 v2 = (if (v1=v2) then Correctly v1 else undefined)"

definition assert_neq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a result" where
  "assert_neq v1 v2 = (if (v1=v2) then undefined else Correctly v2)"

definition assert :: "bool \<Rightarrow> bool result" where
  "assert P = assert_eq P True"

definition assert_not :: "bool \<Rightarrow> bool result" where
  "assert_not P = assert_eq P False"

notation assert ( "assert _" [0] 0) (* this is probably really illegal *)
notation assert_not ( "assert-not _" [0] 0) (* this is probably really illegal *)

value "assert 1+1 = (2::nat)"
value "assert 1+1 = (3::nat)"
value "assert-not 1+1 = (3::nat)"

value "assert_neq None (List.find (%s. fst s = 2) [(1::nat, 10::nat), (2, 20)])"

end