chapter AFP

session Tree_Decomp_Grounding = HOL +
  description \<open>An executable grounder for PDDL tasks based on FastDownward system.\<close>
  options [timeout = 900]
  sessions
	"AI_Planning_Languages_Semantics"
	"Verified_SAT_Based_AI_Planning"
	"HOL-Library"
	"Show"
	"Propositional_Proof_Systems"
  theories [document = false]
    "AI_Planning_Languages_Semantics.PDDL_STRIPS_Semantics"
	"AI_Planning_Languages_Semantics.PDDL_STRIPS_Checker"	
	"AI_Planning_Languages_Semantics.Option_Monad_Add"
	"Verified_SAT_Based_AI_Planning.STRIPS_Semantics"
	"HOL-Library.Sublist"
	"HOL-Library.List_Lexorder"
	"HOL-Library.Char_ord"
	"HOL-Library.Monad_Syntax"
	"Show.Show_Instances"
	"Propositional_Proof_Systems.Sema"
	"Propositional_Proof_Systems.CNF"
    "Propositional_Proof_Systems.CNF_Formulas"
    "Propositional_Proof_Systems.CNF_Sema"
    "Propositional_Proof_Systems.CNF_Formulas_Sema"
  theories [document = false]
    Utils
	Formula_Utils
	Nat_Show_Utils
	String_Utils
	PDDL_Sema_Supplement
	STRIPS_Sema_Supplement	
	PDDL_Checker_Utils
  theories
	DNF
	Graph_Funs
	Normalization_Definitions
	Type_Normalization
	Goal_Normalization
	Precondition_Normalization
	PDDL_Relaxation
	Pseudo_Datalog
	Grounded_PDDL
	PDDL_to_STRIPS
	Grounding_Pipeline
	Running_Example