
# Project Outline
## Formats
- Helmert PDDL format
- Ab+La PDDL format
- My restricted PDDL: Helmert ∩ Ab+La
- Datalog
- (ground PDDL)
- Helmert propositional STRIPS format
- Ab+Ku STRIPS format

## Code project:
- [x] Input: PDDL (Ab+La)
	- doesn't support: axioms, quantified formulas, effects with nested conditions and $\forall$-quantification
- [x] subset of PDDL used as input to grounder
	- MVP: no disjunctions in goal formula
	- MVP: objects/consts must have primitive types. I likely won't lift this restriction.
- [x] Running example (delivery planning problem)
- [ ] Normalization of PDDL
	- [x] Define normalized PDDL: no types, preconditions are conjunctions, (goal is conjunction)
		- [ ] Better: preconditions are in NNF
	- [ ] Type normalization:
		- [x] Algorithm
		- [ ] Proof
			- [ ] ...
	- [ ] Precond normalization:
		- [ ] Definition of NNF
		- [ ] Algorithm
		- [ ] Proof ...
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

### Improvements to MVP

- [ ] rule decomposition with tree decomposition
	- [ ] generate rule graph + proof
	- [ ] tree decomposition = rule decomposition logic
	- [ ] tree decomposition checker
	- [ ] MVP: pipe into external solver
	- [ ] maybe: chose heuristic, implement decomposition algorithm in Isabelle
		- But first search through Isabelle Graph Library for applicable tools
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
