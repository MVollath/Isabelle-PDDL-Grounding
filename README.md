# Verified Grounding of PDDL Tasks using Reachability Analysis (and Tree Decomposition)
A verified Isabelle implementation of the grounder in [Helmert 2009](https://www.sciencedirect.com/science/article/pii/S0004370208001926) for the MVP. The goal is the verification of the improved grounder in [Correa et al 2023](https://ai.dmi.unibas.ch/papers/correa-et-al-icaps2023.pdf).

### Dependencies:
- [AI_Planning_Languages_Semantics](https://www.isa-afp.org/entries/AI_Planning_Languages_Semantics.html): a formalization of PDDL, the input format
- [Verified_SAT_Based_AI_Planning](https://www.isa-afp.org/entries/Verified_SAT_Based_AI_Planning.html): includes a formalization of propositional STRIPS, the output format

### Files
```
Repository
├── Documentation
│   └──thesis.pdf  - - - - - - - The thesis for this project
├── ROOT - - - - - - - - - - - - The ROOT file defining the Isabelle session
├── Running_Example.thy  - - - - A full project demonstration
├── Grounding_Pipeline.thy - - - The central collection of functionality and theorems.
├── ...  - - - - - - - - - - - - other Isabelle theory files
```