# Questions
- How to export Isabelle Code and link with python code?
# Dependencies (tentative):
- [NetworkX](https://networkx.org/documentation/stable/reference/algorithms/generated/networkx.algorithms.approximation.treewidth.treewidth_min_degree.html) (python library):
	- Function `treewidth_min_degree` used for tree decomposition
- Abdulaziz, Ammer, ...: [Isabelle Graph Library](	https://github.com/mabdula/Isabelle-Graph-Library)
- [Ab+La] Abdulaziz, Lammich 2020: [AI Planning Languages Semantics](https://www.isa-afp.org/entries/AI_Planning_Languages_Semantics.html)
	- PDDL formalization in Isabelle
	- my input format
- [Ab+Ku] Abdulaziz, Kurz 2020: [Verified SAT-Based AI Planning ](https://www.isa-afp.org/entries/Verified_SAT_Based_AI_Planning.html) 
	- Includes Isabelle formalization of propositional STRIPS
	- output format of application
- Schlichtkrull et al 2024: [Isabelle-verified correctness of Datalog programs for program analysis](https://github.com/anderssch/LTS-formalization)
	- Isabelle formalization of Datalog semantics and verifier, but not solver.
	- Paper: ([link](https://people.cs.aau.dk/~andsch/SAC2024.pdf))
	- Exact branch from paper: ([source](https://github.com/anderssch/LTS-formalization/tree/SAC2023))

# Sources
### major
- Helmert 2009: [Concise finite-domain representations for PDDL planning tasks](https://www.sciencedirect.com/science/article/pii/S0004370208001926)
	- Main grounder to formally prove!
- Correa et al 2023: [Grounding Planning Tasks Using Tree Decompositions and Iterated Solving](https://ai.dmi.unibas.ch/papers/correa-et-al-icaps2023.pdf)
	- improves Helmert 2009 by tree decomposition and "iterated solving"
- lpopt ([link](https://dbai.tuwien.ac.at/proj/lpopt/))
	- Rule decomposition tool used by Correa
- htd ([link](https://github.com/mabseher/htd/releases/tag/v1.0.0-beta1)),
	- implementation of tree decomposition algorithms used in lpopt
- Bichler 2015: [Optimizing Non-Ground Answer Set Programs via Rule Decomposition](https://dbai.tuwien.ac.at/proj/lpopt/thesis.pdf)
	- lpopt thesis
- Hammerl et al 2015: [Metaheuristic Algorithms and Tree Decomposition](https://www.dbai.tuwien.ac.at/staff/musliu/TreeDecompChap.pdf)
	- Heuristic Tree Decomposition algorithms, used by htd
### minor:
- Calimeri et al 2003: [ASP-Core-2 Input Language Format](https://arxiv.org/pdf/1911.04326)
	- Explanations of transformations of ASP, of which Datalog is a subset
- Dermaku et al 2008: [Heuristic Methods for Hypertree Decomposition ]( https://link.springer.com/chapter/10.1007/978-3-540-88636-5_1)
	- also Tree Decomposition algorithms but Hammerl covers more
- Lifschitz 1987: [On the Semantics of STRIPS]( https://www.semanticscholar.org/paper/ON-THE-SEMANTICS-OF-STRIPS-Lifschitz/83eb0f04037344fde93b3213b790c7824ca09079)
	- Formal definition of STRIPS Semantics, very close to AI_Planning_Languages_Semantics


# Citation Needed
- For every clique, in any tree decomposition, there exists a bag where clique \subseteq bag. Thus, the variable set of any rule can be assigned to a bag.


# Source Notes
## Main Sources
### Isabelle Datalog
- stratified Datalog, meaning there are negations, so it's a bit unnecessarily complicated.
## Tree Decomposition
### lpopt
- tree decomposition heuristics: Default MIW (minimum-degree elimination) ✓, MCS (maximum-cardinality search) ✓, MF (minimum-fill) ✓, NOA (natural) (?).
- decompositions implemented in htd library
### htd
- NaturalOrderingAlgorithm does nothing?
### Metaheuristic algorithms and and tree decomposition
- Describes MIN-DEGREE, MCS, min-fill
### Heuristic Methods for Hypertree Decomposition
- used in Dermaku: MCS, min-fill, (min-induced-width)
### NetworkX
- "The [min-degree] heuristic chooses the nodes according to their degree, i.e., first the node with the lowest degree is chosen, then the graph is updated and the corresponding node is removed. Next, a new node with the lowest degree is chosen, and so on."

## minor
### On the Semantics of STRIPS
- like the definition of PDDL-STRIPS in Ab+La but unclear if everything is grounded or not
	- Allow for arbitrary, even quantified formulas in world model, so long as they can never be invalidated (=invariants)
	- these non-atomic (more generally: non-essential) formulas may be part of ADD so long as they are always invariant (might as well add them to INIT)
	- AI_PLANNING_... uses Definition B


# Explanations with Sources
