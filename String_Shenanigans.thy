theory String_Shenanigans
imports Main
begin

type_synonym asq = string

value "enum :: char list"

value "of_char (CHR 0x00) :: nat"

lemma "of_char c < (256 :: int)"
  by (metis Euclidean_Rings.pos_mod_bound of_char_mod_256 zero_less_numeral)

value "char_of (88 :: nat)"
value "[0 .. 256] :: int list"
lemma "char_of (of_char c) = c" by simp
lemma "(UNIV :: char set) = char_of ` (set [0 .. 256])" sorry

fun ge_str :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "ge_str [] [] \<longleftrightarrow> True" |
  "ge_str s [] \<longleftrightarrow> True" |
  "ge_str [] s \<longleftrightarrow> False" |
  "ge_str (x#xs) (y#ys) \<longleftrightarrow> (
    let x' :: nat = of_char x;
        y' :: nat = of_char y in
    (if x' < y' then False else x' > y' \<or> ge_str xs ys)
)"

value "ge_str ''abcde'' ''bcde''"

fun maxlength :: "string list \<Rightarrow> nat" where
  "maxlength [] = 0" | (* yeah yeah it should be -1 *)
  "maxlength (s # ss) = max (length s) (maxlength ss)"

value "List.replicate 4 True"

definition distinctize :: "string list \<Rightarrow> string list \<Rightarrow> string list" where
  "distinctize blocked new \<equiv>
    (let n = maxlength blocked;
         base = replicate (n + 1) (CHR ''_'') in
    map (append base) new)"

lemma distinctize_dist: "distinct xs \<Longrightarrow> distinct ys \<Longrightarrow> distinct (xs @ distinctize xs ys)"
  sorry

value "distinctize [''lmao'', ''at'', ''from''] [''xd'', ''at'']"

end