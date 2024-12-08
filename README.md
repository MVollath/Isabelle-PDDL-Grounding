# Verified Grounding of PDDL Tasks using Reachability Analysis (and Tree Decomposition)
A verified Isabelle implementation of the grounder in [Helmert 2009](https://www.sciencedirect.com/science/article/pii/S0004370208001926) for the MVP. The goal is the verification of the improved grounder in [Correa et al 2023](https://ai.dmi.unibas.ch/papers/correa-et-al-icaps2023.pdf).

### Dependencies:
- [AI_Planning_Languages_Semantics](https://www.isa-afp.org/entries/AI_Planning_Languages_Semantics.html): a formalization of PDDL, the input format
 - [Verified_SAT_Based_AI_Planning](https://www.isa-afp.org/entries/Verified_SAT_Based_AI_Planning.html): includes a formalization of propositional STRIPS, the output format
 - [LTS-formalization](https://github.com/anderssch/LTS-formalization): a formalization of Datalog, a language used for reachability analysis. Until I figure out how to do imports better, this has to be in the same folder as my repository, and be named "LTS-formalization".

### Repository Walkthrough
- Documentation folder contains a detailed plan of the project, an organized list of sources, and many notes.
- TODO ...