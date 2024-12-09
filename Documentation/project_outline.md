# Project Outline
## Formats
- Helmert PDDL format
- Ab+La PDDL format
- My restricted PDDL: Helmert ∩ Ab+La \ MVP restrictions
- Datalog
- (ground PDDL)
- Helmert propositional STRIPS format
- Ab+Ku STRIPS format

## Code project:
- [x] Input: PDDL (Ab+La)
	- non-numerical, non-temporal fragment. TODO: is it most similar to *PDDL 2.1, level 1*?
	- doesn't support: axioms, $\exists,\forall$-quantified formulas, effects with nested conditions and $\forall$-quantification
	- does add: either types, multiple inheritance, cyclic type-dependencies
- [ ] subset of PDDL used as input to grounder
	- MVP: no disjunctions in goal formula
	- MVP?: objects/consts must have primitive types. I likely won't lift this restriction.
	- MVP: in Ab+La, action signature types aren't checked for  well-formedness. This complicates preconditions for type normalization.
- [x] Running example (delivery planning problem)
- [ ] Normalization of PDDL
	- [x] Define normalized PDDL: no types, preconditions are conjunctions, (goal is conjunction)
		- [ ] Better: preconditions are in NNF
	- [ ] Type normalization:
		- [x] Algorithm
		- [ ] Proof
			- [ ] well-formedness
			- [ ] OG init subset of detyped init, goal unchanged
			- [ ] static predicates
			- [ ] type predicates are static
			- [ ] OG plan action well-formed $\Longleftrightarrow$ detyped plan action well-formed and type preconds satisfied
			- [ ] OG plan action enabled and well-formed $\Longleftrightarrow$ detyped plan-action enabled and well-formed
			- [ ] OG plan action from s to s' $\Longleftrightarrow$ detyped plan action from (s + type preds) to (s' + type preds)
			- [ ] OG plan action solves $\Longleftrightarrow$ detyped plan action solves
	- [ ] Precond normalization:
		- [ ] Definition of NNF
		- [ ] Algorithm
		- [ ] Proof ...
		- Maybe Ab+Ku's CNF logic is useful here.
	- [ ] Putting it together
- [ ] Relaxed-Reachability
	- [ ] Define "relaxed" PDDL: no negative effects or preconditions
	- [ ] Algorithm $\Pi \mapsto \Pi^+$
	- [ ] Proof
		- [ ] Satisfied preconditions can never be invalidated
		- [ ] Reachable in $\Pi \Longrightarrow$ reachable in $\Pi^+$
- [ ] Reachability Analysis
	- [ ] Simple datalog properties
	- [ ] Translation of relaxed problem into Datalog
		- [ ] Ensure rules are safe (correa mentions the Datalog rules are safe due to normalization. How so?)
		- [ ] Prove that: in solution, ground action $A$ is enabled $\longleftrightarrow$ in $\Pi^+$, $A$ is reachable. Same with ground atoms.
	- [ ] *not in MVP:* Simple rule decomposition
		- [ ] Algorithm
		- [ ] Prove equivalence
	- [ ] hook up with external solver
	- [ ] pipe result from external solver with Datalog checker
- [ ] Ground
	- [ ] ground PDDL
		- [ ] Definition: no variables in actions, only constants
		- [ ] Algorithm to generate ground PDDL instance from set of reachable ground atoms + ground actions
		- [ ] Prove equivalence
- [ ] Output: STRIPS (Ab+Ku)
	- Helmert's output is SAS<sup>+</sup>, but I omit the necessary step *invariant synthesis*.
	- [ ] Remove any duplicates in add/del, as Ab+Ku doesn't allow them.
	- [ ] Don't forget that in Ab+Ku, if an operator is not enabled, it does NOOP

### Improvements to MVP

- [ ] rule decomposition with tree decomposition
	- [ ] generate rule graph + proof
	- [ ] tree decomposition = rule decomposition logic
	- [ ] tree decomposition checker
	- [ ] MVP: pipe into external solver
	- [ ] maybe: chose heuristic, implement decomposition algorithm in Isabelle
		- But first search through Isabelle Graph Library for applicable tools
- [ ] pipe STRIPS instance into Ab+Ku's solver
- [ ] allow disjunctions in PDDL goal formulas
	- [ ] compille into conjunctive goal formulas by introducing auxiliary actions and predicates
- [ ] Add goal rule do Datalog program. If that atom isn't enabled by the canonical model, don't even bother grounding the task.
- [ ] *iterated*
	- Start with decomposed Datalog program
	- [ ] remove applicability rules
	- [ ] somehow ensure rule safety??
	- [ ] prove that in solution, ground atom $a$ is enabled $\longleftrightarrow$ in $\Pi^+$, a state with $a$ is reachable.
	- pipe into datalog solver, pipe back into verifier
	- [ ] generate Datalog program to restore ground actions
		- [ ] Proof ...
		- [ ] piping ...
- [ ] *iterated*<sup>≠</sup>
	- [ ] Understand it in the first place lmao
- [ ] Support non-primitive consts/objects
	- lowest priority

### Outlook
- Modify PDDL formalization to support: axioms, $\exists,\forall$-quantified formulas, effects with nested conditions and  ∀-quantification, as in Helmert
- Implement invariant synthesis to change output from STRIPS to a finite-domain representation like SAS<sup>+</sup> (Ab+La's SAS<sup>+</sup> supports axioms)
- (I believe you can consider types in the datalog translation, so you have to generate fewer rules when esuring rule safety. Like for $H(x, y)\leftarrow P(x)$, you would only have to generate $H(x, y_k)\leftarrow\dots$ for those $y_k$ for which the type matches.)
**nvm** i think rule safety is ensured differently
