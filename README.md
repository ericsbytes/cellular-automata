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

## Short Background

A **cellular automaton** or (**CA** for short) is composed of the following:

- A grid of cells that have set number of states (like on = 1 and off = 0)
- A rule that is applied to the configuration of the cells at each "step." The rule is applied repeatedly to an initial configuration of cells and its successors (called generations).
- The rule is applied to every single cell in the grid and is constant over time. A popular example is Conway's Game of Life.

Steven Wolfram put together a set of rules for one dimensional cellular automata, which are called elementary cellular automata. In these rules, the cell can either be alive (1) or dead (0). Their states in the next generation is dependent on their immediate neighbors. Wolfram proposed that cellular automata would be the solution to modelling natural systems, including ones in biology, chemistry and physics, rather than traditional mathematics. There are 256 rules in one dimensional cellular automata.

We specifically focused on a concept called the **Garden of Eden**.

> [!NOTE]
> Garden of Eden is a configuration of cells that cannot be reached from other configurations, so essentially it can only be observed as the initial state
>
> Every Garden of Eden contains an **orphan**, and the orphan is the mandatory core pattern of cells that makes the garden of eden unreachable from other states. So there can be multiple gardens of eden that contain the same orphan configuration.

We also utilized the idea of twins.

> [!NOTE]
> Twins are distinct patterns that can be interchanged with each other whenever they happen, and the overall configuration still maps to the same configuration in the next generation.

The Garden of Eden Theorem (Moore and Myhill):

- Cellular automaton in an Euclidean space is locally injective if and only if it is surjective
- Thus it has a Garden of Eden if and only if it has twins
- This also means that every non-local-injective rule has orphan patterns.

## Project Goals

Our project modeled different cellular automata (CA) elementary rules that are only 1D and attempted to investigate properties about Gardens of Eden (GoE), orphans, and surjectivity of rules.

1. **Model working traces of elementary cellular automata rules.**

	> [!WARNING]
	> A visualizer is provided for tracing, but it should **only be used for tracing.** The visualizer is not intended to visualize generated candidates for GoEs or twins. We recommend using the Evaluator and the verification systems in [search.frg](search.frg) and [cellular-automata.test.frg](cellular-automata.test.frg) with the associated [to-board.sh](to-board.sh) file to verify and examine Forge-generated candidates.

	We have successfully modeled elementary rules such as [rule 30](https://en.wikipedia.org/wiki/Rule_30), [90](https://en.wikipedia.org/wiki/Rule_90), [110](https://en.wikipedia.org/wiki/Rule_110), [184](https://en.wikipedia.org/wiki/Rule_184), [73](https://atlas.wolfram.com/01/01/73/), [67](https://atlas.wolfram.com/01/01/67/). You may alter the run commands under **TRACES** section of [`cellular-automata.frg`](cellular-automata.frg) to try out more `BoardStates` and different bitwidths.

2. **Verify properties about rules, such as montonicity, injectivity and addivity.**

	We were able to successfully verify which of the three each rule obeyed. Our model is able to display counter-examples of these instances in when any of them are violated.

3. **Find and verify Gardens of Eden**

	We have partially achieved this goal. Due to reasons that will be explained further in the rest of the `README`, our model's functionality in finding legitimate GoEs is unreliable. On the other hand, our model is very competent in verifying that given configuration of cells are GoEs or not.

4. **Find and verify twins, and their relationship with GoEs**

	This goal was one of our reach goals and is partially achieved. Our model can find _strong_ twins -- configurations that exactly map to the same next gen configuration. We made a strong attempt in finding weak twins and understanding their relationship with GoEs, but were unable to reliably model this behavior due to the reasons that will be further addressed.

Our goals only slightly changed from our initial proposal, which proposed more vague versions of goals 2, 3, and 4 as target and reach goals. We narrowed down our goals significantly into searching for GoEs and twins.

## Project Design

### Overview of Sigs and Predicates

#### Sigs

| Sig          | Purpose                                                                                                                                                                           |
| ------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `BoardState` | Represents state of the board, has a set of coordinates (Int->Int) that contain coordinates of cells that are alive in that state.                                                |
| `Board`      | Represents the board, has a firstState field which is the initial BoardState and next field that maps one BoardState to the next BoardState (mapping one generation to the next). |

#### Predicates

-

### Design "Aha!" Moments

Initially we set up our predicates to look for configurations that cannot have predecessors. But, because Forge is only looking in the given number of `BoardState`s, we were not getting reliable results. For example, forge could be given 8 `BoardState`s to look at and it might think it found a GoE because it found a set of 7 `BoardState`s that cannot be the predecessor to the remaining `BoardState`, but not necessarily because it had explored every single possible `BoardState`s that could be the predecessor to the supposed GoE.

We shifted our approach from finding GoEs to instead focusing on verifying them through testing known GoEs along with GoEs that our model found. Verifying known GoEs is a tractable problem that Forge is able to solve soundly. This is because it fixes the board we're verifying, and looking for a `BoardState` that could have formed the fixed state.

## Limitations

The biggest issues we ran into were due to boundedness of Forge and our misjudgement in what problem we were trying to solve. We initially planned to create a model that would find orphan patterns and GoEs, and that soon proved to be problematic. Our issue is not unique to Forge, but any bounded solver.

We run into a similar issue with finding twins. Two states are considered twin states if a subset of one state could be replaced with another, and they both still form the same pattern. Because this requires reasoning across all possible subset states and superset states, this was simply intractable with Forge.

Our design choices also led to some limitations in our models. First, because of the wraparound function of our grid, rules that wouldn't have GoEs in an infinite grid (e.g. Rule 90) actually had GoEs in our semi-infinite grid. We verified that this is indeed the case using our verifier.

## Further Expansions

Our biggest expansion and next step would be to try modelling this in a CEGIS solver instead to synethesize potential GoEs for CAs. Our goal with this project was to generate and verify candidate solution states, which is exactly what CEGIS solvers inherently are built to do.

## Collaboration

[Eric Wu](https://github.com/ericsbytes/)  
[Jessi Shin](https://github.com/jessiiishin/)  
[Yevhen Burkovskyi](https://github.com/AncientBehemoth-droid)

### AI Use

Our team used Claude Sonnet 4.6 for assistance.

Primarily, this was to verify and debug bugs in our predicates and functions. This included passing in `BoardState` instances and getting Claude to independently verify that the state generated by Forge was indeed a twin or GoE. We primed its responses with papers related to 1D cellular automata.

Additionally, we would also ask Claude for help with certain design choices and implementations. This included asking it to explain missing constraints, and how we ought to write predictions and functions in a way to followed best practices, such as DRY.
