
## Formats, semantics, solvers, libs:
- Datalog Isabelle formalization (Schlichtkrull et al)
- Datalog Solver. Might not exist in Isabelle but it's enough to have a verifier!
- If no datalog in Isabelle, ASP (answer set programming) formalization
- tree decomposition solver: https://networkx.org/documentation/stable/reference/algorithms/generated/networkx.algorithms.approximation.treewidth.treewidth_min_degree.html
- PDDL semantics AI_Planning_Semantics
- STRIPS semantics Verified_SAT_Based_AI_Planning
- graph library

## STEPS:
- PDDL semantics (AI_Planning_Languages_Semantics)
- define subset of PDDL that will be used as input
- normalized PDDL semantics
- PDDL -> normalized PDDL
- omit invariant synthesis
- relaxed-reachable PDDL semantics
- norm PDDL -> relaxed-reachable PDDL

- relaxed-reachable PDDL -> Datalog
- (ensure that rules are safe? Is rule safety really ensured by Helmert's normalization?)
- "iterated": remove applicability rules
- tree decomposition rule decomposition logic
- tree decomposition algorithm if heuristic available
- choose heuristic + implement

- pipe into datalog solver
- "iterated": create Datalog program to restore ground actions
- "iterated": pipe into datalog program
- obtain all ground actions

- ground into STRIPS

## DEPENDENCIES:
- Tree decomposition solver (python library):
	source: https://networkx.org/documentation/stable/reference/algorithms/generated/networkx.algorithms.approximation.treewidth.treewidth_min_degree.html
	- "The [min-degree] heuristic chooses the nodes according to their degree, i.e., first the node with the lowest degree is chosen, then the graph is updated and the corresponding node is removed. Next, a new node with the lowest degree is chosen, and so on.
- Abdulaziz, Ammer, ...: "Isabelle Graph Library"
	https://github.com/mabdula/Isabelle-Graph-Library
- Abdulaziz, Lammich 2020: AI Planning Languages Semantics https://www.isa-afp.org/entries/AI_Planning_Languages_Semantics.html
	PDDL formalization Isabelle
- Abdulaziz, Kurz 2020: Verified SAT-Based AI Planning https://www.isa-afp.org/entries/Verified_SAT_Based_AI_Planning.html
	used for STRIPS formalization, output of goal application
- Schlichtkrull et al 2024: Isabelle-verified correctness of Datalog programs for program analysis. https://people.cs.aau.dk/~andsch/SAC2024.pdf
	Isabelle formalization of Datalog semantics and verifier, but not solver.
	- Source: https://github.com/anderssch/LTS-formalization
		Identical so far but exact branch in paper is: https://github.com/anderssch/LTS-formalization/tree/SAC2023
	- stratified Datalog, meaning there are negations, so it's a bit unnecessarily complicated.

## SOURCES:
- Correa et al 2023: "Grounding Planning Tasks Using Tree Decompositions and Iterated Solving" https://ai.dmi.unibas.ch/papers/correa-et-al-icaps2023.pdf
- Main project to prove!
- Helmert 2009: "Concise finite-domain representations for PDDL planning tasks" https://www.sciencedirect.com/science/article/pii/S0004370208001926
	Basic grounder improved by correa
- lpopt: https://dbai.tuwien.ac.at/proj/lpopt/
	Rule decomposition tool used by Correa
	- tree decomposition heuristics: Default MIW (minimum-degree elimination) \<checkmark>, MCS (maximum-cardinality search) \<checkmark>, MF (minimum-fill) \<checkmark>, NOA (natural) (?).
	- decompositions implemented in htd library
- htd: https://github.com/mabseher/htd/releases/tag/v1.0.0-beta1,
	- implementation of tree decomposition algorithms used in lpopt
	- NaturalOrderingAlgorithm does nothing?
- Bichler 2015: "Optimizing Non-Ground Answer Set Programs via Rule Decomposition" https://dbai.tuwien.ac.at/proj/lpopt/thesis.pdf
	lpopt thesis
- Hammerl et al 2015: Metaheuristic algorithms and tree decomposition https://www.dbai.tuwien.ac.at/staff/musliu/TreeDecompChap.pdf
	Heuristic Tree Decomposition algorithms
	- Describes MIN-DEGREE, MCS, min-fill
minor:
- Calimeri et al 2003: ASP-Core-2 Input Language Format https://arxiv.org/pdf/1911.04326
	Explanations of transformations of ASP
- Dermaku et al 2008: Heuristic Methods for Hypertree Decomposition https://link.springer.com/chapter/10.1007/978-3-540-88636-5_1
	Decomposition explanations
	- used in Dermaku: MCS, min-fill, (min-induced-width)
- Lifschitz 1987: On the Semantics of STRIPS https://www.semanticscholar.org/paper/ON-THE-SEMANTICS-OF-STRIPS-Lifschitz/83eb0f04037344fde93b3213b790c7824ca09079
	Formal definition of STRIPS Semantics
	- like the definition of PDDL-STRIPS in AI_PLANNING_... but unclear if everything is grounded or not
	- Allow for arbitrary, even quantified formulas in world model, so long as they can never be invalidated (=invariants)
	- these non-atomic (more generally: non-essential) formulas may be part of ADD so long as they are always invariant (might as well add them to INIT)
	- AI_PLANNING_... uses Definition B


Citation needed:
- for every clique, in any tree decomposition, there exists a bag where clique $\subseteq$ bag. Thus, the variable set of any rule can be assigned to a bag.