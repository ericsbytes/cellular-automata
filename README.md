# Cellular Automata 🧬

Your README and documentation should contain enough information for the TAs to:

understand your goals and modeling choices (including the "three buckets": core, closely related, and unrelated);
understand how your model works;
run your model; and
understand what you got out of the modeling exercise.
Your README (and all other natural-language materials) should be written by you, not AI. If your README is effusively verbose, we will not be able to use it for grading. If you don't know what's in your README, you are less likely to be able to answer questions about your project.

You can assume that anyone reading the file will be familiar with your project proposal, but additional (human-focused) documentation is always welcome. Here are some examples of lower-level points you might cover:

What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?
What assumptions did you make about scope? What are the limits of your model?
Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?
How should we understand an instance of your model and what your visualization shows (whether custom or default)?

# Short Background

A cellular automaton is composed of the following. A grid of cells that have set number of states (like on = 1 and off = 0), and a rule that is applied to the configuration of the cells at each "step." The rule is applied repeatedly to an initial configuration of cells and its successors (called generations). The rule is applied to every single cell in the grid and is constant over time. A popular example is Conway's Game of Life.

Steven Wolfram put together a set of rules for one dimensional cellular automata, which are called elementary cellular automata. In these rules, the cell can either be alive (1) or dead (0). Their states in the next generation is dependent on their immediate neighbors. Wolfram proposed that cellular automata would be the solution to modelling natural systems, including ones in biology, chemistry and physics, rather than traditional mathematics.

We specifically focused on a concept called the Garden of Eden. 
* Garden of Eden is a configuration of cells that cannot be reached from other configurations, so essentially it can only be observed as the initial state.
* Every Garden of Eden contains an orphan, and the orphan is the mandatory core pattern of cells that makes the garden of eden unreachable from other states. So there can be multiple gardens of eden that contain the same orphan configuration.

We also utilized the idea of twins.
* Twins are distinct patterns that can be interchanged with each other whenever they happen, and the overall configuration still maps to the same configuration in the next generation.

The Garden of Eden Theorem (Moore and Myhill): 
* Cellular automaton in an Euclidean space is locally injective if and only if it is surjective
* Thus it has a Garden of Eden if and only if it has twins
* This also means that every non-local-injective rule has orphan patterns

# Project Goals

Our project modeled different cellular automata (CA) elementary rules that are only 1D and attempted to investigate properties about Gardens of Eden (GoE), orphans, and surjectivity of rules. 

1. Model working traces of elementary cellular automata rules. 
We have successfully modeled elementary rules such as rule 30, 90, 110. You may alter the run commands under TRACES section of cellular-automata.frg to try out more BoardStates and different bitwidths.

2. Find and verify Gardens of Edens
We have partially achieved this goal. Due to reasons that will be explained further in the rest of the README, our model's functionality in finding legitimate GoEs is unreliable. On the other hand, our model is very competent in verifying that given configuration of cells are GoEs or not.

3. Find and verify twins, and their relationship with GoEs
This goal was one of our reach goals and is partially achieved. We made a strong attempt in finding twins and understanding their relationship with GoEs, but were unable to reliably model this behavior due to the reasons that will be further addressed.

# Project Design

## Overview of Sigs and Predicates

### Sigs


### Predicates

### Design "Aha!" Moments
Initially we set up our predicates to look for configurations that cannot have predecessors. But, because forge is only looking in the given number of BoardStates, we were not getting reliable results. For example, forge could be given 8 BoardStates to look at and it might think it found a GoE because it found a set of 7 BoardStates that cannot be the predecessor to the remaining BoardState, but not necessarily because it had explored every single possible BoardStates that could be the predecessor to the supposed GoE.

We shifted our approach from finding 

# Limitations

The biggest issues we ran into were due to boundedness of forge and our misjudgement in what problem we were trying to solve. We initially planned to create a model that would find orphan patterns and GoEs, and that soon proved to be problematic. 

First, because of the wraparound function of our grid, rules that wouldn't have GoEs in an infinite grid (e.g. Rule 90) actually had GoEs in our semi-infinite grid.


# Further Expansions