theory Running_Example
  imports Main
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Checker"
    PDDL_Checker_Utils
    Type_Normalization Goal_Normalization Precondition_Normalization
    PDDL_Relaxation
begin

subsection \<open> Problem Description \<close>

text \<open>
This is the PDDL problem from Helmert 2009, but modified in minor ways.
It makes use of:
  - type hierarchy
  - parameters with Either types
  - non-trivial preconditions
  - multiple inheritance
  - circular type graph
  - negations in preconditions
It doesn't use:
  - Eq in formulas
It can't use, because I restrict that:
  - objects/consts with Either types
\<close>

definition "my_types \<equiv> [
  (''City'', ''object''), (''Movable'', ''object''),
  (''Vehicle'', ''Movable''), (''Parcel'', ''Movable''),
  (''Car'', ''Vehicle''), (''Train'', ''Vehicle''),
  (''R'', ''L''), (''L'', ''R''),
  (''Batmobile'', ''Car''), (''Batmobile'', ''Train'')]"
definition "my_type_names \<equiv> ''object'' # map fst my_types"
(* purposely doing Car/Train instead of only Vehicle, for no reason other than to just use that feature somewhere *)
definition "my_preds \<equiv> [
  PredDecl (Pred ''at'') [Either [''Movable''], Either [''City'']],
  PredDecl (Pred ''in'') [Either [''Parcel''], Either [''Car'', ''Train'']],
  PredDecl (Pred ''road'') [Either [''City''], Either [''City'']],
  PredDecl (Pred ''rails'') [Either [''City''], Either [''City'']]
]"
definition "my_consts \<equiv> [
  (Obj ''A'', Either [''City'']), (Obj ''B'', Either [''City'']),
  (Obj ''C'', Either [''City'']), (Obj ''D'', Either [''City'']),
  (Obj ''E'', Either [''City'']), (Obj ''F'', Either [''City'']),
  (Obj ''G'', Either [''City''])
]"

definition "op_drive \<equiv> Action_Schema ''drive''
  [(Var ''c'', Either [''Car'']), (Var ''from'', Either [''City'']), (Var ''to'', Either [''City''])]
  (And (Atom (predAtm (Pred ''at'') [term.VAR (Var ''c''), term.VAR (Var ''from'')]))
     (Or (Atom (predAtm (Pred ''road'') [term.VAR (Var ''from''), term.VAR (Var ''to'')]))
         (Atom (predAtm (Pred ''road'') [term.VAR (Var ''to''), term.VAR (Var ''from'')]))))
  (Effect
    [Atom (predAtm (Pred ''at'') [term.VAR (Var ''c''), term.VAR (Var ''to'')])]
    [Atom (predAtm (Pred ''at'') [term.VAR (Var ''c''), term.VAR (Var ''from'')])])"
definition "op_choochoo \<equiv> Action_Schema ''choochoo''
  [(Var ''t'', Either [''Train'']), (Var ''from'', Either [''City'']), (Var ''to'', Either [''City''])]
  (And (Atom (predAtm (Pred ''at'') [term.VAR (Var ''t''), term.VAR (Var ''from'')]))
     (Or (Atom (predAtm (Pred ''rails'') [term.VAR (Var ''from''), term.VAR (Var ''to'')]))
         (Atom (predAtm (Pred ''rails'') [term.VAR (Var ''to''), term.VAR (Var ''from'')]))))
  (Effect
    [Atom (predAtm (Pred ''at'') [term.VAR (Var ''t''), term.VAR (Var ''to'')])]
    [Atom (predAtm (Pred ''at'') [term.VAR (Var ''t''), term.VAR (Var ''from'')])])"
(* into has to be Car/Train instead of Vehicle because of the definition of the predicate "in" *)
definition "op_load \<equiv> Action_Schema ''load''
  [(Var ''what'', Either [''Parcel'']), (Var ''where'', Either [''City'']), (Var ''into'', Either [''Car'', ''Train''])]
     (And (Atom (predAtm (Pred ''at'') [term.VAR (Var ''into''), term.VAR (Var ''where'')]))
         (Atom (predAtm (Pred ''at'') [term.VAR (Var ''what''), term.VAR (Var ''where'')])))
  (Effect
    [Atom (predAtm (Pred ''in'') [term.VAR (Var ''what''), term.VAR (Var ''into'')])]
    [Atom (predAtm (Pred ''at'') [term.VAR (Var ''what''), term.VAR (Var ''where'')])])"
definition "op_unload \<equiv> Action_Schema ''unload''
  [(Var ''what'', Either [''Parcel'']), (Var ''from'', Either [''Car'', ''Train'']), (Var ''where'', Either [''City''])]
     (And (Atom (predAtm (Pred ''at'') [term.VAR (Var ''from''), term.VAR (Var ''where'')]))
         (Atom (predAtm (Pred ''in'') [term.VAR (Var ''what''), term.VAR (Var ''from'')])))
  (Effect
    [Atom (predAtm (Pred ''at'') [term.VAR (Var ''what''), term.VAR (Var ''where'')])]
    [Atom (predAtm (Pred ''in'') [term.VAR (Var ''what''), term.VAR (Var ''from'')])])"
(* btw, this is considered well-formed as long as x is not used in precondition or effects *)
definition "op_broken \<equiv> Action_Schema ''broken''
  [(Var ''x'', Either [''n'existe pas''])]
  \<bottom>
  (Effect [] [])"
(* This operator is only there to demonstrate relaxation of action preconditions, since I couldn't think of anything
  better that would make use of negative preconditions.*)
definition "op_build_tracks \<equiv> Action_Schema ''lay_tracks''
  [(Var ''from'', Either [''City'']), (Var ''to'', Either [''City''])]
  (And (Not (Atom (predAtm (Pred ''rails'') [term.VAR (Var ''from''), term.VAR (Var ''to'')])))
       (Not (Atom (predAtm (Pred ''rails'') [term.VAR (Var ''to''), term.VAR (Var ''from'')]))))
  (Effect [Atom (predAtm (Pred ''rails'') [term.VAR (Var ''from''), term.VAR (Var ''to'')])] [])"


definition "my_actions \<equiv> [op_drive, op_choochoo, op_load, op_unload, op_build_tracks]"

definition "my_domain \<equiv> Domain my_types my_preds my_consts my_actions"
value "my_domain"

(* batmobile because why not *)
definition "my_objs \<equiv> [
  (Obj ''c1'', Either [''Car'']),
  (Obj ''c2'', Either [''Car'']),
  (Obj ''c3'', Either [''Car'']),
  (Obj ''t'', Either [''Train'']),
  (Obj ''p1'', Either [''Parcel'']),
  (Obj ''p2'', Either [''Parcel'']),
  (Obj ''batmobile'', Either [''Batmobile''])
]"

definition "my_init \<equiv> [
  Atom (predAtm (Pred ''at'') [Obj ''c1'', Obj ''A'']),
  Atom (predAtm (Pred ''at'') [Obj ''c2'', Obj ''B'']),
  Atom (predAtm (Pred ''at'') [Obj ''c3'', Obj ''G'']),
  Atom (predAtm (Pred ''at'') [Obj ''t'', Obj ''E'']),
  Atom (predAtm (Pred ''at'') [Obj ''p1'', Obj ''C'']),
  Atom (predAtm (Pred ''at'') [Obj ''p2'', Obj ''F'']),
  Atom (predAtm (Pred ''at'') [Obj ''batmobile'', Obj ''D'']),
  Atom (predAtm (Pred ''road'') [Obj ''A'', Obj ''D'']),
  Atom (predAtm (Pred ''road'') [Obj ''B'', Obj ''D'']),
  Atom (predAtm (Pred ''road'') [Obj ''C'', Obj ''D'']),
  Atom (predAtm (Pred ''rails'') [Obj ''D'', Obj ''E'']),
  Atom (predAtm (Pred ''road'') [Obj ''E'', Obj ''F'']),
  Atom (predAtm (Pred ''road'') [Obj ''F'', Obj ''G'']),
  Atom (predAtm (Pred ''road'') [Obj ''G'', Obj ''E''])
]"
definition "my_goal \<equiv>
  And (Atom (predAtm (Pred ''at'') [Obj ''p1'', Obj ''G'']))
      (Atom (predAtm (Pred ''at'') [Obj ''p2'', Obj ''E'']))"

definition "my_problem \<equiv> Problem my_domain my_objs my_init my_goal"

lemma wf_d1: "ast_domain.wf_domain my_domain"
  by (intro wf_domain_intro) eval

lemma wf_p1: "ast_problem.wf_problem my_problem"
  by (intro wf_problem_intro) eval

subsection \<open> Execution \<close>

definition "my_plan \<equiv> [
  PAction ''drive'' [Obj ''c1'', Obj ''A'', Obj ''D''],
  PAction ''drive'' [Obj ''c1'', Obj ''D'', Obj ''C''],
  PAction ''load'' [Obj ''p1'', Obj ''C'', Obj ''c1''],
  PAction ''drive'' [Obj ''c1'', Obj ''C'', Obj ''D''],
  PAction ''unload'' [Obj ''p1'', Obj ''c1'', Obj ''D''],  
  PAction ''choochoo'' [Obj ''t'', Obj ''E'', Obj ''D''],
  PAction ''load'' [Obj ''p1'', Obj ''D'', Obj ''t''],  
  PAction ''choochoo'' [Obj ''t'', Obj ''D'', Obj ''E''],
  PAction ''unload'' [Obj ''p1'', Obj ''t'', Obj ''E''],

  PAction ''drive'' [Obj ''c3'', Obj ''G'', Obj ''F''],
  PAction ''load'' [Obj ''p2'', Obj ''F'', Obj ''c3''],
  PAction ''drive'' [Obj ''c3'', Obj ''F'', Obj ''E''],
  PAction ''unload'' [Obj ''p2'', Obj ''c3'', Obj ''E''],

  PAction ''load'' [Obj ''p1'', Obj ''E'', Obj ''c3''],
  PAction ''drive'' [Obj ''c3'', Obj ''E'', Obj ''G''],
  PAction ''unload'' [Obj ''p1'', Obj ''c3'', Obj ''G''],

  PAction ''choochoo'' [Obj ''batmobile'', Obj ''D'', Obj ''E''],
  PAction ''drive'' [Obj ''batmobile'', Obj ''E'', Obj ''G'']
]" (* Just taking the batmobile for a spin at the end, for fun. *)

value "enab_exec_x my_problem
  (PAction ''drive'' [Obj ''c1'', Obj ''A'', Obj ''D'']) (set my_init)"

value "valid_plan_x my_problem my_plan"
lemma "ast_problem.valid_plan my_problem my_plan"
  by (intro valid_plan_intro[OF wf_p1]) eval


subsection \<open> Type normalization \<close>


lemma "ast_domain.restrict_dom my_domain" by eval

(* Type system shenanigans *)
value "of_type_x my_domain (Either []) (Either [])"
value "of_type_x my_domain (Either []) (Either [''FOO''])" (* even though FOO doesn't exist *)
value "of_type_x my_domain (Either [''FOO'', ''BAR'']) (Either [''BAR'', ''FOO''])" (* even though both don't exist *)
value "of_type_x my_domain (Either [''R'']) (Either [''object''])"

declare ast_domain.constT_def [code]
declare ast_problem.objT_def [code]

value "ast_domain.is_of_type' (ast_problem.objT my_problem)
  (ast_domain.STG my_domain) (Obj ''c1'') (Either [''Car'', ''FOO''])" (* even though FOO doesn't exist *)

(* type normalization testing *)
value "showvals (reachable_nodes my_types) my_type_names"
value "ast_domain.type_preds my_domain"
value "ast_domain.supertype_facts_for my_domain (my_objs ! 1)"
value "ast_domain.type_precond my_domain (Var ''into'', Either [''Car'', ''Train''])"
value "ast_domain.detype_ac my_domain op_load"
value "detype_preds my_preds"

definition "my_dom_detyped \<equiv> ast_domain.detype_dom my_domain"
value "my_dom_detyped"
definition "my_prob_detyped \<equiv> ast_problem.detype_prob my_problem"
value "my_prob_detyped" (* Important *)

(* also follows from restr_problem2.detype_prob_wf *)
lemma wf_p2: "ast_problem.wf_problem my_prob_detyped"
  by (intro wf_problem_intro) eval

value "enab_exec_x my_prob_detyped
  (my_plan ! 0) (ast_problem.I my_prob_detyped)"

lemma "ast_problem.valid_plan my_prob_detyped my_plan"
  by (intro valid_plan_intro[OF wf_p2]) eval

subsection \<open> Goal normalization \<close>

definition "my_dom_degoaled \<equiv> ast_problem.degoal_dom my_prob_detyped"
definition "my_prob_degoaled \<equiv> ast_problem.degoal_prob my_prob_detyped"
value "my_prob_degoaled" (* Important *)
lemma wf_p3: "ast_problem.wf_problem my_prob_degoaled"
  by (intro wf_problem_intro) eval

definition "my_plan_2 \<equiv> my_plan @ [ast_domain.\<pi>\<^sub>g my_dom_detyped]"
value my_plan_2
value "valid_plan_x my_prob_degoaled my_plan" (* missing goal planaction *)
lemma "ast_problem.valid_plan my_prob_degoaled my_plan_2"
  by (intro valid_plan_intro[OF wf_p3]) eval

subsection \<open> Precondition normalization \<close>

value "ast_domain.prefix_padding my_dom_degoaled"
value "ast_domain.split_ac_names my_dom_degoaled op_drive 5"
value "ast_domain.split_ac my_dom_degoaled op_drive"
value "ast_domain.split_acs my_dom_degoaled"
definition "my_dom_split \<equiv> ast_domain.split_dom my_dom_degoaled"
definition "my_prob_split \<equiv> ast_problem.split_prob my_prob_degoaled"
value "my_dom_split"
value "my_prob_split" (* Important *)
lemma wf_p4: "ast_problem.wf_problem my_prob_split"
  by (intro wf_problem_intro) eval

(* A little manual labor to decide which one of the split actions
  corresponds to which step in the original plan. *)
definition "my_plan_3 \<equiv> [
  PAction ''1_drive'' [Obj ''c1'', Obj ''A'', Obj ''D''],
  PAction ''0_drive'' [Obj ''c1'', Obj ''D'', Obj ''C''],
  PAction ''1_load'' [Obj ''p1'', Obj ''C'', Obj ''c1''],
  PAction ''1_drive'' [Obj ''c1'', Obj ''C'', Obj ''D''],
  PAction ''1_unload'' [Obj ''p1'', Obj ''c1'', Obj ''D''],  
  PAction ''0_choochoo'' [Obj ''t'', Obj ''E'', Obj ''D''],
  PAction ''0_load'' [Obj ''p1'', Obj ''D'', Obj ''t''],  
  PAction ''1_choochoo'' [Obj ''t'', Obj ''D'', Obj ''E''],
  PAction ''0_unload'' [Obj ''p1'', Obj ''t'', Obj ''E''],

  PAction ''0_drive'' [Obj ''c3'', Obj ''G'', Obj ''F''],
  PAction ''1_load'' [Obj ''p2'', Obj ''F'', Obj ''c3''],
  PAction ''0_drive'' [Obj ''c3'', Obj ''F'', Obj ''E''],
  PAction ''1_unload'' [Obj ''p2'', Obj ''c3'', Obj ''E''],

  PAction ''1_load'' [Obj ''p1'', Obj ''E'', Obj ''c3''],
  PAction ''0_drive'' [Obj ''c3'', Obj ''E'', Obj ''G''],
  PAction ''1_unload'' [Obj ''p1'', Obj ''c3'', Obj ''G''],

  PAction ''1_choochoo'' [Obj ''batmobile'', Obj ''D'', Obj ''E''],
  PAction ''0_drive'' [Obj ''batmobile'', Obj ''E'', Obj ''G''],

  PAction ''0_Goal_______'' []
]"

(* if you choose the wrong plan action at one point, this tells you where *)
value "valid_plan_x my_prob_split my_plan_3"

value "enab_exec_x my_prob_split
  (my_plan_3 ! 0) (ast_problem.I my_prob_split)"
lemma "ast_problem.valid_plan my_prob_split my_plan_3"
  by (intro valid_plan_intro[OF wf_p4]) eval

(* And this is how you would reconstruct the original plan from a plan obtained for the normalized
instance: *)

definition "restored_plan \<equiv>
  let p2 = ast_domain.restore_plan_split my_dom_degoaled my_plan_3 in
  ast_domain.restore_plan_degoal my_dom_detyped p2"
value "restored_plan" (* important *)
lemma "ast_problem.valid_plan my_problem restored_plan"
  by (intro valid_plan_intro[OF wf_p1]) eval

subsection \<open> PDDL Relaxation \<close>
(* The only action with impacted preconditions is op_build_tracks *)
value "actions (my_dom_split) ! 9"
value "relax_ac (actions (my_dom_split) ! 9)"
(* and here's a modified effect: *)
value "actions (my_dom_split) ! 1"
value "relax_ac (actions (my_dom_split) ! 1)"

definition "my_dom_relaxed \<equiv> ast_domain.relax_dom my_dom_split"
definition "my_prob_relaxed \<equiv> ast_problem.relax_prob my_prob_split"
value my_prob_relaxed (* Important *)
lemma wf_p5: "ast_problem.wf_problem my_prob_relaxed"
  by (intro wf_problem_intro) eval

(* note that a plan is still valid after relaxation *)
lemma "ast_problem.valid_plan my_prob_relaxed my_plan_3"
  by (intro valid_plan_intro[OF wf_p5]) eval

end