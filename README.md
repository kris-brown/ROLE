# ROLE
Code related to Research on Logical Expressivism, as described in [Reasons for Logic, Logic for Reasons](https://www.amazon.com/Reasons-Logic-Pragmatics-Semantics-Conceptual/dp/1032360763) and Brandom's [seminar on logic](https://sites.pitt.edu/~rbrandom/Courses/2024%20Philosophy%20of%20Language/Language%20and%20Reasons%202024%20Main.html).

## Features

- Declare implication frames + interpretation functions
- Compute implicational roles and operations like $\sqcup$ and $\preceq$
- Compute logical operations on conceptual contents
- Compute content entailment among conceptual contents
  - Use this to determine $\mathbb{I}_X$ given a lexicon $\mathcal{L}_X$, an implication frame $Y$, and an interpretation function $\mathcal{L}_X \rightarrow \mathbb{C}_Y$.

## Roadmap

The next things I want to implement: 

- Automated morphism search 
  - Category of implication frames and interpretation functions
  - Various flavors of 'simple' maps which send bearers to bearers
- (Co)-limits of implication frames (in the above categories)
- Ryan's scorekeeping dynamics  
- Notebook showing classical tautologies (e.g. Pierce's law) hold in frames (even nonmonotonic ones) which satisfy containment. 
- Distinguishing from traditional nonmonotonic logics
  - Nonmonotonicity of incoherence, cautious monotonicity / cumulative transitivity failures
  - See Shopper's Guide

## Documentation and Tests

One runs the test suite with the following command:

```
julia --project test/runtests.jl
```

To locally build the documentation and the literate code examples, run the following in the command line:
```
julia --project=docs -e "using ROLE, LiveServer; servedocs(literate_dir=\"docs/literate\",skip_dir=\"docs/src/generated\")"
```

## NOTE

This library is currently under active development, and so is not yet at a point where a constant API/behavior can be assumed. That being said, if this project looks interesting/relevant please contact me at kris@topos.institute!
