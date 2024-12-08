
# Questions
**Isabelle**
- How to export Isabelle Code and link with python code?
- Is there a function `"('a × 'a) list ⇒ ('a × 'a) list"` that turns a relation into its (reflexive) transitive closure? I wrote one but it's not fully optimized.
- What does `declare my_lemma [code]` do? Why would a lemma be turned into SML?
- What does `context fixes ty_ent` do if context has no name?
- `no_notation my_fun (infixl "+" 65)`?

**Ab+La**
- Where is the PDDL parser?
- "flat type hierarchy"?
**Orga**
- Can this project become part of the AFP? What would I need to watch out for? Can something be in AFP with external dependencies (Datalog formalization is not in AFP)?
# Dependencies (tentative):
- [NetworkX](https://networkx.org/documentation/stable/reference/algorithms/generated/networkx.algorithms.approximation.treewidth.treewidth_min_degree.html) (python library):
	- Function `treewidth_min_degree` used for tree decomposition
- Abdulaziz, Ammer, ...: [Isabelle Graph Library](	https://github.com/mabdula/Isabelle-Graph-Library)
- [Ab+La] Abdulaziz, Lammich 2020: [AI Planning Languages Semantics](https://www.isa-afp.org/entries/AI_Planning_Languages_Semantics.html)
	- PDDL formalization in Isabelle
	- format of input to my program
	- Paper: ([link](https://mabdula.github.io/papers/verifiedValidator.pdf))
- [Ab+Ku] Abdulaziz, Kurz 2020: [Verified SAT-Based AI Planning ](https://www.isa-afp.org/entries/Verified_SAT_Based_AI_Planning.html) 
	- Includes Isabelle formalization of propositional STRIPS
	- output format of application
	- Paper: ([link](https://kclpure.kcl.ac.uk/ws/portalfiles/portal/189846427/verified_SAT_plan.pdf))
- Schlichtkrull et al 2024: [Isabelle-verified correctness of Datalog programs for program analysis](https://github.com/anderssch/LTS-formalization)
	- Isabelle formalization of Datalog semantics and verifier, but not solver.
	- Paper: ([link](https://people.cs.aau.dk/~andsch/SAC2024.pdf))
	- Exact branch from paper: ([source](https://github.com/anderssch/LTS-formalization/tree/SAC2023))

# Sources
### major:
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
- For every clique, in any tree decomposition, there exists a bag where clique $\subseteq$ bag. Thus, the variable set of any rule can be assigned to a bag.


# Source Notes
## Main Sources
### Helmert
- [ ] detailed dissection currently at **6. Grounding**
- Helmert's effects can have nested effects and $\forall$-quantification
### Correa
- [x] fully dissected
- (**double check**) Can ground more problems in total because of good space efficiency, but is comparatively time inefficient.
- Iterated<sup>≠</sup> is confusing...

### Ab+La
- [x] fully dissected code
- [ ] fully dissected paper

**Issues:**
- In `wf_problem`, action schema parameters aren't checked for `wf_type`, meaning their types are allowed to be invalid.
- `Either []` is allowed. Subtype of everything, but supertype of nothing but itself. *Joker* if object, unsatisfiable if parameter.
- Type graph allowed to have cycles. Not everything inherits `''object''`.

**PDDL Semantics**
- STRIPS formulas: no negation (including no implication). Satisfied STRIPS formula can't be invalidated by setting atoms to true. Unsatisfied STRIPS formula can't become satisfied by setting atoms to false.
- Domain has consts, instance ("problem") has objects. Same concept.
- Where formulas are restricted to a list of atoms, `atom formula list` is used in favor of e.g. `PredAtom list/set`
- `term`: Union of variable and object
- preconditions and goal formulas can have any structure
- add overwrites del effects

**Lifschitz Consistency**
- Definition of system according to Lifschitz 1987, definition "B".

**SASP Semantics**
- SAS<sup>+</sup> effects have, in addition to regular effect conditions, specific preconditions for a modified variable's previous value. Affect whether the entire operator is enabled, weirdly enough. Apparently leftover relic.
- Execution can be undefined, yet `lookup_operator` bothers with returning `optional`

### Isabelle Datalog
- [ ] fully dissected
- Stratified Datalog, meaning there are negations, so it's a bit unnecessarily complicated.

### Ab+Ku
- [x] fully dissected

**State-Var Rep**
- state `'var ⇀ 'domain`, assignment `('var × 'domain)` which is converted to state, effect `('var × 'domain) list`

**STRIPS Representation**
- STRPS state: `'var ⇀ bool`. Every variable must explicitly be assigned True/False. Checked for init.
- operator: pre, add, del `:: 'var list`
- effects are turned into `('var × bool) list`
- `is_valid_operator_strips` ensures no overlap between add and del effects! If allowed, add still overwrites del.
- goal can contain negative literals

**STRIPS Semantics**
- Serial plan execution: if operator isn't enabled, **it does NOOP!**
- A parallel plan is a plan where each step has a list of operators that do not interfere with each other, i.e. their order of operation would not matter. Not necessary for me.

**CNF**
- Might be useful for formula normalization (even though I want NNF instead of Helmert's CNF)
- `datatype 'a literal = Pos 'a | Neg 'a`
- Syntax sugar `3⁺ :: int literal`
- `'a clause` = `'a literal set`

**Map supp**
- function graph logic `[(x, f x), ...]`. Might prove useful for translating modified actions...

## Tree Decomposition
### lpopt
- [ ] fully dissected
- tree decomposition heuristics: Default MIW (minimum-degree elimination) ✓, MCS (maximum-cardinality search) ✓, MF (minimum-fill) ✓, NOA (natural) (?).
- decompositions implemented in htd library
### htd
- [ ] fully dissected
- NaturalOrderingAlgorithm does nothing?
### Metaheuristic Algorithms and Tree Decomposition
- [ ] fully dissected
- Describes MIN-DEGREE, MCS, min-fill
### Heuristic Methods for Hypertree Decomposition
- [ ] fully dissected
- used in Dermaku: MCS, min-fill, (min-induced-width)
### NetworkX
- [ ] fully dissected
- "The [min-degree] heuristic chooses the nodes according to their degree, i.e., first the node with the lowest degree is chosen, then the graph is updated and the corresponding node is removed. Next, a new node with the lowest degree is chosen, and so on."

## minor
### Lifschitz
- [x] fully dissected
- like the definition of PDDL-STRIPS in Ab+La but unclear if everything is grounded or not
	- Allow for arbitrary, even quantified formulas in world model, so long as they can never be invalidated (=invariants)
	- these non-atomic (more generally: non-essential) formulas may be part of ADD so long as they are always invariant (might as well add them to init, then?)
	- Ab+La uses Definition B


# Explanations (with citations)
### Why consts/objects should have primitive types
TODO