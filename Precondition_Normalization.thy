theory Precondition_Normalization
imports "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
    PDDL_Sema_Supplement Utils String_Shenanigans DNF
begin

definition "n_clauses ac \<equiv> length (dnf_list (ac_pre ac))"
abbreviation "max_length' xs \<equiv> Max (length ` set xs)"

context ast_domain begin

definition "max_n_clauses \<equiv> Max (set (map n_clauses (actions D)))"
definition "prefix_padding \<equiv> max_length' (distinct_strings max_n_clauses) + 1"

fun (in -) set_n_pre :: " ast_action_schema \<Rightarrow> string \<Rightarrow> term atom formula \<Rightarrow> ast_action_schema" where
  "set_n_pre (Action_Schema _ params _ eff) n pre
  = Action_Schema n params pre eff"

definition "split_ac_names ac \<equiv>
  map (\<lambda>prefix. pad prefix_padding prefix @ ac_name ac)
    (distinct_strings (n_clauses ac))"

definition split_ac :: "ast_action_schema \<Rightarrow> ast_action_schema list" where
  "split_ac ac =
    (let clauses = dnf_list (ac_pre ac) in
    map2 (set_n_pre ac) (split_ac_names ac) clauses)"

definition "split_acs \<equiv> concat (map split_ac (actions D))"

definition "split_dom \<equiv>
  Domain
    (types D)
    (predicates D)
    (consts D)
    split_acs"

definition (in ast_problem) "split_prob \<equiv>
  Problem
    split_dom
    (objects P)
    (init P)
    (goal P)"

(* it's important to be able to convert a plan for the output problem into a plan for the input problem.
  The other direction is probably (hopefully?) not important. *)
fun restore_pa_split where
  "restore_pa_split (PAction n args) = PAction (drop prefix_padding n) args"
abbreviation "restore_plan_split \<pi>s \<equiv> map restore_pa_split \<pi>s"

definition (in ast_domain) "precond_normed_dom \<equiv>
  \<forall>ac \<in> set (actions D). is_conj (ac_pre ac)"

definition (in ast_problem) "precond_normed_prob \<equiv> precond_normed_dom"

end

section \<open> Precondition Normalization Proofs \<close>

text \<open> locale setup for simplified syntax \<close>

abbreviation (in ast_domain) (input) "D4 \<equiv> split_dom"
abbreviation (in ast_problem) (input) "P4 \<equiv> split_prob"

locale ast_domain4 = ast_domain
sublocale ast_domain4 \<subseteq> d4: ast_domain D4 .

locale wf_ast_domain4 = wf_ast_domain
sublocale wf_ast_domain4 \<subseteq> d4: ast_domain D4 .
sublocale wf_ast_domain4 \<subseteq> ast_domain4 .

locale ast_problem4 = ast_problem
sublocale ast_problem4 \<subseteq> p4: ast_problem P4 .
sublocale ast_problem4 \<subseteq> ast_domain4 D .

locale wf_ast_problem4 = wf_ast_problem
sublocale wf_ast_problem4 \<subseteq> p4 : ast_problem P4.
sublocale wf_ast_problem4 \<subseteq> ast_problem4 .
sublocale wf_ast_problem4 \<subseteq> wf_ast_domain4 D
  by unfold_locales

text \<open> Alternate definitions \<close>

(* probably unnecessary *)
lemma set_n_pre_alt: "set_n_pre ac n pre =
  Action_Schema n (ac_params ac) pre (ac_eff ac)"
  by (cases ac) simp

(* probably unnecessary *)
lemma set_n_pre_sel [simp]:
  "ac_name (set_n_pre ac n pre) = n"
  "ac_params (set_n_pre ac n pre) = ac_params ac"
  "ac_pre (set_n_pre ac n pre) = pre"
  "ac_eff (set_n_pre ac n pre) = ac_eff ac"
  using set_n_pre_alt by simp_all

lemma (in -) set_n_pre_mapsel:
  assumes "length ns = length pres"
  shows
    "map ac_name (map2 (set_n_pre ac) ns pres) = ns"
    (*"map ac_params (map2 (set_n_pre ac) ns pres) = replicate (n_clauses ac) (ac_params ac)" *)
    "map ac_pre (map2 (set_n_pre ac) ns pres) = pres"
using assms by (induction ns pres rule: list_induct2) simp_all

lemma (in ast_domain) split_dom_sel [simp]:
  "types D4 = types D"
  "predicates D4 = predicates D"
  "consts D4 = consts D"
  "actions D4 = split_acs"
  using split_dom_def by simp_all

lemma (in ast_problem) split_prob_sel [simp]:
  "domain P4 = D4"
  "objects P4 = objects P"
  "init P4 = init P"
  "goal P4 = goal P"
  using split_prob_def by simp_all

text \<open> Action splitting properties \<close>
lemma (in ast_domain) split_ac_len:
  "length (split_ac ac) = length (dnf_list (ac_pre ac))"
  "length (split_ac_names ac) = length (dnf_list (ac_pre ac))"
  unfolding split_ac_def split_ac_names_def n_clauses_def by simp_all

lemma (in ast_domain) split_ac_nth:
  assumes "i < length (dnf_list (ac_pre ac))"
  shows "split_ac ac ! i =
    Action_Schema
      (pad prefix_padding (unique_string i) @ ac_name ac)
      (ac_params ac)
      (dnf_list (ac_pre ac) ! i)
      (ac_eff ac)"
  using assms unfolding split_ac_def split_ac_names_def n_clauses_def
  by (cases ac) simp

lemma (in ast_domain4) p_ac:
  "ac' \<in> set (actions D4) \<longleftrightarrow> (\<exists>ac \<in> set (actions D). ac' \<in> set (split_ac ac))"
  unfolding split_dom_sel split_acs_def by simp

lemma (in ast_domain) split_pres: "map ac_pre (split_ac a) = dnf_list (ac_pre a)"
    unfolding split_ac_def Let_def apply (rule set_n_pre_mapsel)
    unfolding split_ac_names_def n_clauses_def by simp

(* "ac_params a' = ac_params a" "ac_eff a' = ac_eff a" if "a' \<in> set (split_ac a)" *)


lemma (in ast_domain) split_ac_sel:
  assumes "a' \<in> set (split_ac a)"
  shows
    "\<exists>i < length (split_ac a). ac_name a' = pad prefix_padding (unique_string i) @ ac_name a"
    "ac_params a' = ac_params a"
    "ac_pre a' \<in> set (dnf_list (ac_pre a))"
    "ac_eff a' = ac_eff a"
proof -
  from assms show "ac_params a' = ac_params a" "ac_eff a' = ac_eff a"
    unfolding split_ac_def Let_def by auto
  from assms obtain i where i: "i < length (split_ac a)" "a' = split_ac a ! i"
    using in_set_conv_nth by metis
  from i show "ac_pre a' \<in> set (dnf_list (ac_pre a))"
    using split_ac_nth split_ac_len(1) by simp
  from i show "\<exists>i < length (split_ac a). ac_name a' = pad prefix_padding (unique_string i) @ ac_name a"
    using split_ac_nth split_ac_len(1) by auto
qed

subsection \<open> Output format \<close>

lemma (in ast_problem4) prec_normed_ac:
  "\<forall>ac' \<in> set (split_ac ac). is_conj (ac_pre ac')"
  using split_ac_sel(3) dnf_list_conjs by auto

subsection \<open> Well-formedness \<close>

context ast_domain4 begin

lemma p_wf_type: "d4.wf_type = wf_type"
  apply (rule ext)
  subgoal for x
    by (cases x; simp)
  done

lemma p_wf_pred_decl: "d4.wf_predicate_decl = wf_predicate_decl"
  apply (rule ext)
  subgoal for x                                      
    apply (cases x; simp) using p_wf_type by simp
  done

lemma p_constT: "d4.constT = constT"
  unfolding ast_domain.constT_def by simp

lemma (in ast_problem4) p_objT: "p4.objT = objT"
  unfolding ast_problem.objT_def using p_constT by simp

lemma p_sig: "d4.sig = sig"
  unfolding ast_domain.sig_def by simp

lemma p_subtype_rel: "d4.subtype_rel = subtype_rel"
  unfolding ast_domain.subtype_rel_def by simp

lemma p_of_type: "d4.of_type = of_type"
  unfolding ast_domain.of_type_def using p_subtype_rel by simp

lemma p_is_of_type: "d4.is_of_type = is_of_type"
  unfolding ast_domain.is_of_type_def using p_of_type by metis

lemma p_wf_atom: "d4.wf_atom = wf_atom"
  apply (rule ext; rule ext)
  subgoal for tyt x
    apply (cases x; simp)
    using split_dom_sel(1-2) p_sig p_is_of_type by metis
  done

lemma p_wf_fmla: "d4.wf_fmla = wf_fmla"
  unfolding ast_domain.wf_fmla_alt using p_wf_atom by metis

lemma p_wf_eff: "d4.wf_effect = wf_effect"
  unfolding ast_domain.wf_effect_alt ast_domain.wf_fmla_atom_alt
  using p_wf_fmla by metis

lemma (in ast_problem4) p_wf_wm: "p4.wf_world_model = wf_world_model"
  unfolding ast_problem.wf_world_model_def ast_domain.wf_fmla_atom_alt
  using p_wf_fmla p_objT split_prob_sel(1) by metis

end
context wf_ast_domain4 begin

(* generated action IDs are distinct *)
(* TODO: simplify; combine with split_ac_sel *)

lemma (in ast_domain) split_names_prefix_length:
  assumes "ac \<in> set (actions D)" "n \<in> set (split_ac_names ac)"
  shows "\<exists>p. length p = prefix_padding \<and> n = p @ ac_name ac"
proof -
  from assms(2)[unfolded split_ac_names_def] obtain p where
    pin: "p \<in> set (distinct_strings (n_clauses ac))" and
    n: "n = pad prefix_padding p @ ac_name ac"
    by auto

  have "n_clauses ac \<le> max_n_clauses"
    using max_n_clauses_def assms(1) by simp
  hence "prefix (distinct_strings (n_clauses ac)) (distinct_strings (max_n_clauses))"
    using distinct_strings_prefix by (metis le_Suc_ex)
  hence "set (distinct_strings (n_clauses ac)) \<subseteq> set (distinct_strings (max_n_clauses))"
    using set_mono_prefix by auto
  hence "length p \<le> prefix_padding"
    unfolding prefix_padding_def
    apply (intro trans_le_add1)
    using pin by auto (* I'm relieved auto solves that *)
  hence "length (pad prefix_padding p) = prefix_padding"
    using pad_length(1) by auto
  thus ?thesis using n by simp
qed

lemma (in ast_domain) split_names_distinct:
  shows "distinct (split_ac_names ac)"
proof -
  have "split_ac_names ac =
    map (\<lambda>p. p @ ac_name ac) (map (pad prefix_padding) (distinct_strings (n_clauses ac)))"
    unfolding split_ac_names_def by simp
  thus ?thesis using distinct_strings_padded append_r_distinct by metis
qed

lemma (in wf_ast_domain) split_names_disjoint:
  assumes "ac \<in> set (actions D)" "ac' \<in> set (actions D)" "ac_name ac \<noteq> ac_name ac'"
  shows "set (split_ac_names ac) \<inter> set (split_ac_names ac') = {}"
  apply (unfold disjoint_iff_not_equal)
  using assms split_names_prefix_length
  using append_eq_append_conv by metis

(* TODO generalize to Utils:
  distinct xs \<Longrightarrow> x \<noteq> y; \<in> set xs \<longrightarrow> f x \<inter> f y = {} \<Longrightarrow> distinct (removeAll ... *)
lemma (in wf_ast_domain) split_names_dist_nonempty:
  "distinct (removeAll [] (map split_ac_names (actions D)))"
proof -
  have "distinct (removeAll [] (map split_ac_names as))"
    if "distinct (map ac_name as)" "set as \<subseteq> set (actions D)" for as
    using that
  proof (induction as)
    case (Cons a as)
    thus ?case proof (cases "split_ac_names a = []")
      case False

      from Cons.prems have ain: "\<forall>a' \<in> set as. a' \<in> set (actions D)" "a \<in> set (actions D)" by auto

      from Cons that have "\<forall>n \<in> set (map ac_name as). ac_name a \<noteq> n" by auto
      hence "\<forall>a' \<in> set as. ac_name a' \<noteq> ac_name a" by auto
      with ain have "\<forall>a' \<in> set as. set (split_ac_names a) \<inter> set (split_ac_names a') = {}"
        using split_names_disjoint by blast
      hence "\<forall>s \<in> set (removeAll [] (map split_ac_names as)). set (split_ac_names a) \<inter> set s = {}" by auto
      with False have "split_ac_names a \<notin> set (removeAll [] (map split_ac_names as))" by blast
      then show ?thesis using False Cons by simp
    qed (simp add: Cons)
    
  qed simp
  thus ?thesis using wf_D(6) by simp
qed

lemma (in wf_ast_domain) split_names_disjoint2:
  assumes "xs \<in> set (map split_ac_names (actions D))"
          "ys \<in> set (map split_ac_names (actions D))"
          "xs \<noteq> ys"
        shows "set xs \<inter> set ys = {}"
proof -
  from assms obtain x y where
    xy: "xs = split_ac_names x"  "x \<in> set (actions D)"
        "ys = split_ac_names y"  "y \<in> set (actions D)" by auto
  hence "x \<noteq> y" using assms(3) by blast
  hence "ac_name x \<noteq> ac_name y" using wf_D xy
    by (meson distinct_map_eq)
  thus ?thesis
    using split_names_disjoint xy by simp
qed

lemma (in ast_domain4) p_ac_names:
  "map ac_name (actions D4) = concat (map split_ac_names (actions D))"
proof -
  have l: "length (split_ac_names ac) = length (dnf_list (ac_pre ac))" for ac
    unfolding split_ac_names_def n_clauses_def by simp

  have "map ac_name (actions D4) = concat
      (map (map ac_name) (map split_ac (actions D)))"
    unfolding split_dom_sel split_acs_def
    using map_concat by metis
  also have "... = concat
      (map (map ac_name \<circ> split_ac) (actions D))" by simp
  also have "... = concat (map split_ac_names (actions D))"
    unfolding split_ac_def comp_def
    using set_n_pre_mapsel(1) l by simp
  finally show ?thesis .
qed

lemma split_ac_names_dist:
  "distinct (map ac_name (actions D4))"
  unfolding p_ac_names distinct_concat_iff
  using split_names_dist_nonempty split_names_distinct split_names_disjoint2 by auto

(* action well-formedness *)

lemma p_actions_wf: "list_all1 d4.wf_action_schema (actions D4)"
proof
  fix a' assume assm: "a' \<in> set (actions D4)"
  then obtain a where a: "a \<in> set (actions D)" "a' \<in> set (split_ac a)" using p_ac by auto
  hence "atoms (ac_pre a') \<subseteq> atoms (ac_pre a)" using split_ac_sel(3) dnf_list_atoms by metis
  hence fmla_wf: "d4.wf_fmla tyt (ac_pre a')" if "wf_fmla tyt (ac_pre a)" for tyt
    unfolding p_wf_fmla
    using that ast_domain.wf_fmla_alt p_wf_fmla by blast

  have "d4.wf_action_schema a'" if "wf_action_schema a"
    using that unfolding ast_domain.wf_action_schema_alt
    using a(2) split_ac_sel p_constT fmla_wf p_wf_eff by metis

  thus "d4.wf_action_schema a'" using a(1) wf_D by simp
qed

theorem (in wf_ast_domain4) p_dom_wf: "d4.wf_domain"
  unfolding d4.wf_domain_def split_dom_sel
  unfolding p_wf_type p_wf_pred_decl
  using wf_D split_ac_names_dist p_actions_wf ast_domain.wf_types_def by simp_all

theorem (in wf_ast_problem4) p_prob_wf: "p4.wf_problem"
  unfolding p4.wf_problem_def split_prob_sel
  unfolding p_wf_type p_wf_wm p_wf_fmla p_objT
  using wf_P p_dom_wf by simp_all

end

subsection \<open> Semantics \<close>

context wf_ast_problem4 begin

lemma dnf_list_cw:
  assumes "wm_basic M"
  shows "M \<^sup>c\<TTurnstile>\<^sub>= F \<longleftrightarrow> (\<exists>c\<in>set (dnf_list F). M \<^sup>c\<TTurnstile>\<^sub>= c)"
  using assms valuation_iff_close_world dnf_list_semantics by blast

text \<open> Applying a map to dnf_list \<close>

lemma (in -) neg_of_lit_map: "map_formula m (neg_of_lit l) = neg_of_lit (map_literal m l)"
  by (cases l) simp_all

lemma (in -) neg_conj_of_clause_map: "map_formula m (neg_conj_of_clause c)
  = neg_conj_of_clause (map (map_literal m) c)"
  unfolding neg_conj_of_clause_def
  apply (induction c) apply simp using neg_of_lit_map by auto
  
lemma (in -) neg_conj_of_clause_map2: "map ((map_formula m) \<circ> neg_conj_of_clause) D
  = map neg_conj_of_clause (map (map (map_literal m)) D)"
  using neg_conj_of_clause_map by auto

lemma (in -) nnf_map: "map_formula m (nnf F) = nnf (map_formula m F)"
  by (induction F rule: nnf.induct) auto

(* there's gotta be some easier way to prove this *)
(* this works for all g where "f (g x y) = g (f x) (f y)" *)
lemma (in -) append_prod_map:
  "map (map f) [x @ y. x \<leftarrow> xs, y \<leftarrow> ys] = [x @ y. x \<leftarrow> map (map f) xs, y \<leftarrow> map (map f) ys]"
proof -
  define m where "m = map f"
  have aux: "map (\<lambda>x. f (g x)) xs = map f (map g xs)" for f g xs by simp

  (* "map f [x @ y. x \<leftarrow> xs, y \<leftarrow> ys] = map f (concat (map (\<lambda>x. map ((@) x) ys) xs))" *)
  have "map m [x @ y. x \<leftarrow> xs, y \<leftarrow> ys] = (concat (map (map m) (map (\<lambda>x. map ((@) x) ys) xs)))"
    using map_concat by blast
  also have "... = concat (map ((map m) \<circ> (\<lambda>x. map ((@) x) ys)) xs)" by simp
  also have "... = concat (map (\<lambda>x. map m (map ((@) x) ys)) xs)" by (meson comp_apply)
  also have "... = concat (map (\<lambda>x. map (m \<circ> ((@) x)) ys) xs)" by simp
  also have "... = concat (map (\<lambda>x. map (\<lambda>y. m (x @ y)) ys) xs)"
    by (metis fun_comp_eq_conv[of m])
  also have "... = concat (map (\<lambda>x. map (\<lambda>y. m x @ m y) ys) xs)"
    unfolding m_def by simp
  also have "... = concat (map (\<lambda>x. map (\<lambda>y. m x @ y) (map m ys)) xs)"
    using aux by metis
  also have "... = concat (map (\<lambda>x. map (\<lambda>y. x @ y) (map m ys)) (map m xs))"
    using aux[of "(\<lambda>x. map (\<lambda>y. x @ y) (map m ys))"] by metis
  finally show ?thesis unfolding m_def by simp
qed

lemma (in -) cnf_lists_map:
  assumes "is_nnf F"
  shows "map (map (map_literal m)) (cnf_lists F) = cnf_lists (map_formula m F)"
  using assms proof (induction F rule: cnf_lists.induct)
  case (6 F G)
    define mp where "mp = (map (map_literal m))"
    have "map mp (cnf_lists (F \<^bold>\<or> G)) = map mp [f @ g. f \<leftarrow> (cnf_lists F), g \<leftarrow> (cnf_lists G)]" by simp
    also have "... = [f @ g. f \<leftarrow> map mp (cnf_lists F), g \<leftarrow> map mp (cnf_lists G)]"
      unfolding mp_def using append_prod_map by auto
    also have "... = [f @ g. f \<leftarrow> cnf_lists (map_formula m F), g \<leftarrow> cnf_lists (map_formula m G)]"
      using 6 unfolding mp_def by fastforce
    finally show ?case unfolding mp_def by simp
qed simp_all

lemma dnf_list_map: "map (map_formula m) (dnf_list F) = dnf_list (map_formula m F)"
proof -
  have "map (map_formula m) (dnf_list F)
    = map (map_formula m) (map neg_conj_of_clause (cnf_lists (nnf (\<^bold>\<not> F))))"
    unfolding dnf_list_def ..
  also have "... = map ((map_formula m) \<circ> neg_conj_of_clause) (cnf_lists (nnf (\<^bold>\<not> F)))"
    by simp
  also have "... = map neg_conj_of_clause (map (map (map_literal m)) (cnf_lists (nnf (\<^bold>\<not> F))))"
    using neg_conj_of_clause_map by auto
  also have "... = map neg_conj_of_clause (cnf_lists (map_formula m (nnf (\<^bold>\<not> F))))"
    using cnf_lists_map by (metis is_nnf_nnf)
  also have "... = map neg_conj_of_clause (cnf_lists (nnf (\<^bold>\<not> (map_formula m F))))"
    using nnf_map formula.map(3) by metis
  finally show ?thesis unfolding dnf_list_def by simp
qed

(* end map *)

term ac_tsubst
term resolve_instantiate
term instantiate_action_schema
term map_atom_fmla

lemma
  "A \<Turnstile> ac_pre a \<longleftrightarrow> (\<exists>a' \<in> set (split_ac a). A \<Turnstile> ac_pre a')"
proof -
  let ?dnf = "dnf_list (ac_pre a)"
  have "A \<Turnstile> ac_pre a \<longleftrightarrow> (\<exists>p' \<in> set ?dnf. A \<Turnstile> p')"
    using dnf_list_semantics by blast
  also have "... \<longleftrightarrow> (\<exists>i < length ?dnf. A \<Turnstile> ?dnf ! i)"
    using in_set_conv_nth by metis
  also have "... \<longleftrightarrow> (\<exists>i < length ?dnf. A \<Turnstile> ac_pre (split_ac a ! i))"
    using split_ac_nth by auto
  also have "... \<longleftrightarrow> (\<exists>a' \<in> set (split_ac a). A \<Turnstile> ac_pre a')"
    using in_set_conv_nth split_ac_len by metis
  finally show ?thesis by simp
qed

lemma
  assumes "wm_basic M"
  shows "M \<^sup>c\<TTurnstile>\<^sub>= precondition (instantiate_action_schema a args) \<longleftrightarrow>
    (\<exists>a' \<in> set (split_ac a). M \<^sup>c\<TTurnstile>\<^sub>= precondition (instantiate_action_schema a' args))"
proof -
  oops  

lemma "a \<in> set (actions D) \<Longrightarrow> \<exists>n. resolve_action_schema n = Some a"
  by (simp add: res_aux)


(* TODO move to Utils *)
(* kind of useless, saves a a line or two sometimes *)
lemma (in -) list_induct_n:
  assumes "length xs = n" "P [] 0"
  "\<And>x xs n. length xs = n \<Longrightarrow>
  P xs n \<Longrightarrow> P (x # xs) (Suc n)" shows "P xs n"
using assms proof (induction xs arbitrary: n)
  case (Cons x xs n)
  thus ?case by (cases n) simp_all
qed simp

(* TODO move to Utils *)
lemma (in -) drop_prefix:
  assumes "length xs = n" shows "drop n (xs @ ys) = ys"
  by (induction rule: list_induct_n[OF assms]) simp_all

lemma restore_split_ac:
  assumes "a \<in> set (actions D)" "a' \<in> set (split_ac a)"
  shows "drop prefix_padding (ac_name a') = ac_name a"
proof -
  (* TODO simplify the start *)
  from assms obtain i where i: "split_ac a ! i = a'" "i < length (split_ac a)"
    by (meson in_set_conv_nth)
  hence "ac_name a' \<in> set (map ac_name (split_ac a))" by auto
  hence "ac_name a' \<in> set (split_ac_names a)"
    unfolding split_ac_def
    using split_ac_len set_n_pre_mapsel by metis
  thus ?thesis
    using assms split_names_prefix_length drop_prefix by metis
qed

thm restore_pa_split.simps
(*(drop prefix_padding ?n)*)
thm split_ac_nth
thm dnf_list_semantics

end


subsection \<open> Code Setup \<close>

lemmas precond_norm_code =
  n_clauses_def
  ast_domain.max_n_clauses_def
  ast_domain.prefix_padding_def
  ast_domain.split_ac_names_def
  ast_domain.split_ac_def
  ast_domain.split_acs_def
  ast_domain.split_dom_def
  ast_problem.split_prob_def
  ast_domain.restore_pa_split.simps
declare precond_norm_code[code]

end