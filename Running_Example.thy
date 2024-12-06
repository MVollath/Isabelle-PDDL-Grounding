theory Running_Example
  imports PDDL_Normalization AbLa_Code Testing_Hacks
    (*"AI_Planning_Languages_Semantics.PDDL_STRIPS_Checker"*)
begin

(*
Ideally, a an example domain makes use of:
  - type hierarchy
  - "Either" type
  - complex preconditions
  - eq/neq
*)

(* design issues:
  roads aren't symmetric so the preconditions will have to be. *)

definition "my_types \<equiv> [
  (''City'', ''object''), (''Movable'', ''object''),
  (''Vehicle'', ''Movable''), (''Parcel'', ''Movable''),
  (''Car'', ''Vehicle''), (''Train'', ''Vehicle''),
  (''R'', ''L''), (''L'', ''R''),
  (''Batmobile'', ''Car''), (''Batmobile'', ''Train'')]"
definition "my_type_names \<equiv> ''object'' # map fst my_types"
(* purposely doing Car/Train instead of only Vehicle, for no reason other than to just use it somewhere *)
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
  [(Var ''into'', Either [''Car'', ''Train'']), (Var ''what'', Either [''Parcel'']), (Var ''where'', Either [''City''])]
     (And (Atom (predAtm (Pred ''at'') [term.VAR (Var ''into''), term.VAR (Var ''where'')]))
         (Atom (predAtm (Pred ''at'') [term.VAR (Var ''what''), term.VAR (Var ''where'')])))
  (Effect
    [Atom (predAtm (Pred ''in'') [term.VAR (Var ''what''), term.VAR (Var ''into'')])]
    [Atom (predAtm (Pred ''at'') [term.VAR (Var ''what''), term.VAR (Var ''where'')])])"
definition "op_unload \<equiv> Action_Schema ''unload''
  [(Var ''from'', Either [''Car'', ''Train'']), (Var ''what'', Either [''Parcel'']), (Var ''where'', Either [''City''])]
     (And (Atom (predAtm (Pred ''at'') [term.VAR (Var ''from''), term.VAR (Var ''where'')]))
         (Atom (predAtm (Pred ''in'') [term.VAR (Var ''what''), term.VAR (Var ''from'')])))
  (Effect
    [Atom (predAtm (Pred ''at'') [term.VAR (Var ''what''), term.VAR (Var ''where'')])]
    [Atom (predAtm (Pred ''in'') [term.VAR (Var ''what''), term.VAR (Var ''from'')])])"



definition "my_actions \<equiv> [op_drive, op_choochoo, op_load, op_unload]"

definition "my_domain \<equiv> Domain my_types my_preds my_consts my_actions"
(*value "ast_domain.wf_domain my_domain"*)


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
  Atom (predAtm (Pred ''at'') [Obj ''batmobile'', Obj ''E'']),
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

definition
  "showvals f xs \<equiv> map (\<lambda>x. (x, f x)) xs"

value "assert wf_domain_c my_domain"
value "assert wf_problem_c my_problem"

(* type normalization debugging *)
value "showvals (reachable_nodes my_types) my_type_names"
value "type_preds my_domain"
value "pred_for_type my_domain ''Car''"
value "supertype_preds my_domain ''Car''"
value "supertype_facts_for my_domain (my_objs ! 1)"
value "type_precond my_domain (Var ''into'', Either [''Car'', ''Train''])"
value "detype_ac my_domain op_load"
value "detype_preds my_preds"
value "detype_dom my_domain"
value "assert wf_domain_c (detype_dom my_domain)"
value "detype_prob my_problem"
value "assert wf_problem_c (detype_prob my_problem)"

value "of_type_c my_domain (Either []) (Either [])"
value "of_type_c my_domain (Either []) (Either [''Car'', ''FOO''])"
value "of_type_c my_domain (Either [''FOO'', ''BONK'']) (Either [''BAR'', ''FOO''])"
value "of_type_c my_domain (Either [''R'']) (Either [''object''])"
value "is_of_type_c my_domain (objT_c my_problem)
  (Obj ''c1'') (Either [''Car'', ''FOO''])"

end