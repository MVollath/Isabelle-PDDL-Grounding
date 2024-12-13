Some of the markdown formatting doesn't work on github. It does on [stackedit.io](stackedit.io/app)
# Questions
**Isabelle**
- in unstructured proof, how to replace all occurrences of something with new variable? (this generalizes the proof, but sometimes you can do it)
- `fun "detype_pred (PredDecl p argts) = PredDecl p (transform argts)"` into `lemma "detype_pred p = PredDecl (pred p) (transform (argTs p))"`. Like what I did with `detype_ac_def`. It's a sort of unfolding.
- Is there a function `"('a × 'a) list ⇒ ('a × 'a) list"` that turns a relation into its (reflexive) transitive closure? I wrote one but it's not fully optimized.

**Ab+La**
- Where is the PDDL parser?
- "flat type hierarchy"?
- How to execute code in PDDL_STRIPS_Checker? I always get:
`"List.coset" is not a constructor, on left hand side of equation, in theorem:
insert ?x (List.coset ?xs) ≡ List.coset (removeAll ?x ?xs)`

**Orga**
- Scope: What's the minimum to pass? And what would give me my desired grade?
- Can this project become part of the AFP? What would I need to watch out for? Can something be in AFP with external dependencies (Datalog formalization is not in AFP)?

**minor**
- How to export Isabelle Code and link with python code?
- What does `declare my_lemma [code]` do? Why would a lemma be turned into SML?
- `no_notation my_fun (infixl "+" 65)`?

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
	- Paper: ([link](https://arxiv.org/pdf/2010.14648))
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

### probably not
- S. Edelkamp, M. Helmert, Exhibiting knowledge in planning problems to minimize state encoding length
	- earlier grounder by Helmert, to STRIPS. Almost same output format as my project

# Citation Needed
- For every clique, in any tree decomposition, there exists a bag where clique $\subseteq$ bag. Thus, the variable set of any rule can be assigned to a bag.
	- [Stackexchange](https://math.stackexchange.com/questions/1227867/a-clique-in-a-tree-decomposition-is-contained-in-a-bag)


# Source Notes
- "lifted" $\leftrightarrow$ "grounded"
## Main Sources
### <ins>Helmert</ins>
- [ ] detailed dissection currently at **6. Grounding**
- *Fast Downward* (FD) planning system
- Good running example: delivery problem
- Propositional STRIPS exactly like my previous project. States are sets of true atoms. Ab+Ku only introduces neagtive atoms in the goal.
- SAT-based solvers apparently prefer finite-doain inputs over STRIPS
- **"Invariant synthesis and grounding are not related to one another and could just as well be performed in the opposite order."**
- My project: Task generation is final step and generates STRIPS instead of FDR. Afterwards (outlook?), invariant synthesis may be used to turn binary variables into FD ones.

**PDDL format**
- PDDL format 2.2 "level 1": non-numerical, non-temporal fragment of PDDL
- Operators $\langle \chi, e\rangle$. Precondition, effect
	- Effects can have nested conditions and $\forall$-quantification. Example syntax: $\forall x: (\mathit{is\\\_wet}\  x) \triangleright (\neg\mathit{burns}\ x)$
	- Operator parameters are the free variables of precondition $\chi$ and effect $e$.
- Axioms $\varphi\leftarrow\psi$: Derive predicates that are automatically updated.
	- $\varphi$ is an atom, $\psi$ a formula.
	- Axioms have to be safe: $\mathit{free}\ \psi\subseteq\mathit{free}\ \varphi$
	- Axioms "stratifiable" (valid) iff: There exists a total preorder over predicates such that $\forall Q, P: Q\in\varphi\land P\in\psi\Longrightarrow Q\succeq P$. Even $Q \succ P$ if $P$ is negated in the NNF of $\psi$.
	- Stratifiability necessary for axiom evaluation. $P \prec Q$ means $P$ is not dependent on $Q$, and is thus evaluated first.
	- Fluent predicates (occur in effects/init) must not appear in axiom heads.
- PDDL task: $\langle$ init, goal, axioms, operators $\rangle$. Predicates including their arity are implicitly defined. Types not explicitly part of this formalism, but still supported by normalization later.

**Finite-Domain Representation FDR**
- Based on SAS<sup>+</sup> with axioms and conditional effects.
- A grounded planning format where variables are not binary. Instead, every variable has a respective finite and discrete domain.
- Formulas only have conjunctions
- No nexted conditional effects
- Axioms $\mathit{cond}\rightarrow\mathit{var}:=\mathit{val}$
	- $\mathit{cond}$ is just a partial assignment
	- Derived variables' domains contain default value $\bot$
	- Axiom layering: Each axiom part of a "layer". Bottom axiom layer evaluated first, then next and so on. Values can be overriden in higher layers, but not in the same layer.
	- No contradictions within same layer: If $v:=d$ is in a head, $v$ must not appear in the same layer with any other value than $d$, even in bodies.
- State space is directed graph. Node is state, edge is transition.

**Normalization**
- Compile away types: A tiny bit easier for me because we don't allow $\forall$ in effects.
- Goal must be conjunction: **Axioms required to compile disjunctions into conjunctions**, but we can use auxiliary operators too.
- For preconditions, turn formula into CNF then split into multiple operators across disjunctions. **NNF may be enough due to properties of STRIPS formulas, then no need to split operators.**

**Datalog generation**
- Datalog is declarative programming language for logic
- straight forward. $\mathit{A\\\_applicable}(\cdot)\leftarrow\mathit{A\\\_pre}(\cdot)$
$\mathit{A\\\_effect_i}(\cdot)\leftarrow\mathit{A\\\_applicable}(\cdot)$
- How can you ensure that this is "safe"? What if my action just doesn't have preconditions? Can you have an (implicit) $\forall$-quantifier in the head?
	- Rules are never unsafe here, because you always have type-preconditions for every variable. If the reader wants to build this for un-typed PDDL, they can add $\mathit{dummy}(x)$ in the body where needed. The dummy predicate is contained in the facts for every constant.
	- Alternative: $H(x, y)\leftarrow P(x)$ is illegal, so you might do
$H_{\forall2}(x)\leftarrow P(x)$ and then add many rules
$H(x, y_k) \leftarrow H_{\forall2}(x)$

**Datalog rule decomposition**
- Definition 14: I can probably explain this a little more elaborately.
- ...
- Problem: how to choose joins. Helmert chooses atoms with many variables (**TODO** find quote. This is a claim by Correa).

### <ins>Correa</ins>
- [x] fully dissected
- (**double check**) Can ground more problems in total because of good space efficiency, but is comparatively time inefficient due to overhead.
- Iterated<sup>≠</sup> is confusing...
- Grounding simplifies a problem from first-order logic to propositional logic.

**PDDL stuff**
- $\neq$ treated as static built-in predicate by e.g. gringo (also by Ab+La)

**Logic Programs**
- More general: *Answer Set Programming* (ASP)
- More restrictive: *I think* Stratified Datalog. Only allows single atom in head.
- More restrictive: Datalog. Doesn't allow negative atoms.
- Logic program $\mathcal L =\langle\mathcal F, \mathcal R\rangle$
	- $\mathcal F$: facts
	- $\mathcal R$: set of disjunctive rules like
$r:=\underbrace{H_1 \lor \dots\lor H_k}_{\mathit{head(r)}}\leftarrow\underbrace{P_1, \dots, P_n}_{\mathit{body}^{+}(r)}, \underbrace{\neg N_1, \dots, \neg N_m}_{\mathit{body}^{-}(r)}$
	- "All rules we considered are safe"? I.e. $\mathit{free}(\mathit{head}(r))\subseteq \mathit{free}(\mathit{body}(r))$. Otherwise, too many atoms would follow from one body instantiation.
	- Atoms can have a mix of constants and variables. $\mathcal F$ contains ground atoms only.
	- A stable model $\mathcal M$ is a solution and satisfies each fact and each rule. (And all facts, aside from the initial facts, are derived from rules.)
- "each Datalog program has a unique stable model M, called the *canonical model*". Can be iteratively constructed from $\mathcal F$. **TODO this doesn't apply to stratified Datalog, right?**

**Datalog Translation**
- Add goal rule. If goal isn't reachable, don't even bother grounding the program.

**Simple Rule Decomposition**
- Simple join/projection decompositions: "different choices on how to decompose rules will lead to a different number of temporary predicates." Correa claims preferring atoms with few variables yields better results, whereas Helmert prefers atoms with many variables (page 3 footnote 2).
- Join decomposition: If $q_1(\cdot), q_2(\cdot)\in\mathit{body}$, create new predicate with rule $\mathit{temp}(\cdot)\leftarrow q_1(\cdot), q_2(\cdot)$. **Improvement**: If we strictly follow Definition 14 in Helmert, if $v\in\mathit{free}(q_1)\cap\mathit{free}(q_2)$ does not appear elsewhere in the original $\mathit{body}$, then we can omit $v$ from the parameters of $\mathit{temp}$.
- Projection: Find an atom $q$ in a body that uses a variable $v$ unused elsewhere in the rule, then add $\mathit{temp}(\cdot\backslash v)\leftarrow q(\cdot)$. This reduces variable count by essentially resolving existential qualifiers. E.g.: $Q(\mathit{room})\leftarrow\mathit{holding}(\mathit{box}),\mathit{at}(\mathit{room})$ is simplified by introducing $\mathit{holding\\\_any\\\_box}()\leftarrow\mathit{holding}(\mathit{box})$

**Advanced Rule Decomposition with Tree Decomp**
- Rule $r$ gets primal graph $G_r=\langle V, E\rangle$ where $V=\mathit{vars}(r), (v_1, v_2)\in E \Leftrightarrow \exists P(t)\in\mathit{head}(r)\cup\mathit{body}(r): v_1, v_2\in\mathit{vars}(t)$. $P$ is a predicate and the terms $t$ the parameters.
- Tree decompose this graph. Many rules have low tree width, hence efficient grounding if good decomposition is found.
- lpopt generates "n new rules": Probably a mistake, you need more rules for disjunctions.
- Tree width can only be 1 (primal graph uncyclic) if every pred in the body has only 2 variables.

**iterated**
- Avoid grounding actions at first by skilling applicability rules and instead directly feeding into action effect rules ("simplified" problem). Create a separate rule for each (add) effect.
- This only immediately generates reachable atoms, not ground actions.
- Trivial solution: unify preconditions and explode exponentially
- Actual solution: iterated solving: Solve the simplified problem, obtain solution $\mathcal M$. For every action, create new program with facts $\mathcal F := \mathcal M$ and "choice rules".
- **TODO clean this up:** encode type predicates as $\mathbf1\{V_i-\mathit{assign}(x):\mathit{type\\\_T}(x)\}\mathbf1$. If no type predicates, I think you can choose any unary pred from the body.
For non-ground atom $q_i$ in body with variables $V_{\dots k}$ create $\bot\leftarrow \mathit{v_{1}\\\_ assign}(x_1), \dots, \mathit{v_k\\\_assign}(x_k), \neg q_i(x_1, \dots, x_k)$.
But how can he use negation? Is it not Datalog but ASP/stratified Datalog?
- Each stable model is then one ground action. Iteratively solve and enumerate all of them.
- **?**: When removing applicability rules, the result isn't safe necessarily. 

**iterated<sup>≠</sup>**
- "negated static predicates" why is ≠ negated? It can just be a predicate, why would FD not already consider it in the simplified problem?
→ Inequalities only considered in second phase (action enumeration) because of tree with. This is probably why they receive special treatment.

### <ins>Ab+La</ins>
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
- $\neq$ is a type of formula atom. It is essentially a built-in, static predicate.

**Lifschitz Consistency**
- Definition of system according to Lifschitz 1987, definition "B".

**SASP Semantics**
- SAS<sup>+</sup> effects have, in addition to regular effect conditions, specific preconditions for a modified variable's previous value. Affect whether the entire operator is enabled, weirdly enough. Apparently leftover relic.
- Execution can be undefined, yet `lookup_operator` bothers with returning `optional`

### <ins>Isabelle Datalog</ins>
- [ ] fully dissected
- Stratified Datalog, meaning there are negations, so it's a bit unnecessarily complicated.

### <ins>Ab+Ku</ins>
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
### <ins>lpopt</ins>
- [ ] fully dissected
- tree decomposition heuristics: Default MIW (minimum-degree elimination) ✓, MCS (maximum-cardinality search) ✓, MF (minimum-fill) ✓, NOA (natural) (?).
- decompositions implemented in htd library
### <ins>htd</ins>
- [ ] fully dissected
- NaturalOrderingAlgorithm does nothing?
### <ins>Metaheuristic Algorithms and Tree Decomposition</ins>
- [ ] fully dissected
- Describes MIN-DEGREE, MCS, min-fill
### <ins>Heuristic Methods for Hypertree Decomposition</ins>
- [ ] fully dissected
- used in Dermaku: MCS, min-fill, (min-induced-width)
### <ins>NetworkX</ins>
- [ ] fully dissected
- "The [min-degree] heuristic chooses the nodes according to their degree, i.e., first the node with the lowest degree is chosen, then the graph is updated and the corresponding node is removed. Next, a new node with the lowest degree is chosen, and so on."

## minor
### <ins>Lifschitz</ins>
- [x] fully dissected
- like the definition of PDDL-STRIPS in Ab+La but unclear if everything is grounded or not
	- Allow for arbitrary, even quantified formulas in world model, so long as they can never be invalidated (=invariants)
	- these non-atomic (more generally: non-essential) formulas may be part of ADD so long as they are always invariant (might as well add them to init, then?)
	- Ab+La uses Definition B


# Explanations
### Why consts/objects should have primitive types
TODO

### Rule Decomposition Examples
Join decompositions can remove $y$ from head eventually, because $r$ does not contain $y$.
$r(x, z, w) \leftarrow \underbrace{p(x, y), q(x, y)}_{pq}, s(y, z), t(z, w, v)$
1. $pq(x, y) \leftarrow p(x, y), q(x, y)$ | valid join rule
$r(x, z, w) \leftarrow \underbrace{pq(x, y), s(y, z)}_{pqs}, t(z, w, v)$
2. $pqs(x, z) \leftarrow pq(x, y), s(y, z)$ | valid join rule
$r(x, z, w) \leftarrow pqs(x, z), \underbrace{t(z, w, v)}_{t_{\exists3}}$
3. $t_{\exists 3}(z, w)\leftarrow t(z, w, v)$ | valid projection rule
$r(x, z, w) \leftarrow pqs(x, z), t_{\exists3}(z, w)$ | valid join rule

There's also the concept of variable-uniqueness where variable repetition like $p(x, y, x)$ isn't allowed. **TODO how is that ensured?** Probably by modifying the predicates and facts in a preprocessing step?

**Why relaxed reachability**
If you allow negative atoms, previously derived atoms could become false in the future.  You would need reassignments, which would greatly complicate the iterative Datalog solver.