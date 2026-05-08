# Cellular Automata 🧬

## Short Background

A **cellular automaton** or (**CA** for short) is composed of the following:

- A grid of cells that have set number of states (like on = 1 and off = 0)
- A rule that is applied to the configuration of the cells at each "step." The rule is applied repeatedly to an initial configuration of cells and its successors (called generations).
- The rule is applied to every single cell in the grid and is constant over time. A popular example is Conway's Game of Life.

Steven Wolfram put together a set of rules for one dimensional cellular automata, which are called elementary cellular automata. In these rules, the cell can either be alive (1) or dead (0). Their states in the next generation is dependent on their immediate neighbors. Wolfram proposed that cellular automata would be the solution to modelling natural systems, including ones in biology, chemistry and physics, rather than traditional mathematics. There are 256 rules in one dimensional cellular automata.

We specifically focused on a concept called the **Garden of Eden**.

> [!IMPORTANT]
> Garden of Eden is a configuration of cells that cannot be reached from other configurations, so essentially it can only be observed as the initial state
>
> Every Garden of Eden contains an **orphan**, and the orphan is the mandatory core pattern of cells that makes the garden of eden unreachable from other states. So there can be multiple gardens of eden that contain the same orphan configuration.

We also utilized the idea of **twins**.

> [!IMPORTANT]
> Twins are distinct patterns that can be interchanged with each other whenever they happen, and the overall configuration still maps to the same configuration in the next generation.
>
> In our project, we distinguish between so-called "weak" twins and "strong" twins. Weak twins are essentially two states that share the exact same next state (e.g. the pre-image of some state). Strong twins are two states that share the same next state with the added requirement that they have identical non-zero superset alive cells.

> [!NOTE]
> **The Garden of Eden Theorem (Moore and Myhill):**
>
> - Cellular automaton in an Euclidean space is locally injective if and only if it is surjective
> - Thus it has a Garden of Eden if and only if it has twins
> - This also means that every non-local-injective rule has orphan patterns.

## Project Goals

Our project modeled different cellular automata (CA) elementary rules that are only 1D and attempted to investigate properties about Gardens of Eden (GoE), orphans, and surjectivity of rules.

1. **Model working traces of elementary cellular automata rules.**

    We have successfully modeled elementary rules such as [rule 30](https://en.wikipedia.org/wiki/Rule_30), [90](https://en.wikipedia.org/wiki/Rule_90), [110](https://en.wikipedia.org/wiki/Rule_110), [184](https://en.wikipedia.org/wiki/Rule_184), [73](https://atlas.wolfram.com/01/01/73/), [67](https://atlas.wolfram.com/01/01/67/). You may alter the run commands under **TRACES** section of [`cellular-automata.frg`](cellular-automata.frg) to try out more `BoardStates` and different bitwidths.

2. **Verify properties about rules, such as montonicity, injectivity and addivity.**

    We were able to successfully verify which of the three each rule obeyed. Our model is able to display counter-examples of these instances in when any of them are violated.

3. **Find and verify Gardens of Eden**

    We have partially achieved this goal. Due to reasons that will be explained further in the rest of the `README`, our model's functionality in finding legitimate GoEs is unreliable. On the other hand, our model is very competent in verifying that given configuration of cells are GoEs or not.

4. **Find and verify twins, and their relationship with GoEs**

    This goal was one of our reach goals and is partially achieved. Our model can find _strong_ twins -- configurations that exactly map to the same next gen configuration. We made a strong attempt in finding weak twins and understanding their relationship with GoEs, but were unable to reliably model this behavior due to the reasons that will be further addressed.

Our goals only slightly changed from our initial proposal, which proposed more vague versions of goals 2, 3, and 4 as target and reach goals. We narrowed down our goals significantly into searching for GoEs and twins.

## Project Design

### File Guide

| File                                                       | Description                                                     |
| ---------------------------------------------------------- | --------------------------------------------------------------- |
| [`cellular-automata.frg`](cellular-automata.frg)           | General predicates for modelling cellular automata rules.       |
| [`cellular-automata.test.frg`](cellular-automata.test.frg) | Tests general predicates.                                       |
| [`search.frg`](search.frg)                                 | Assertions meant to search for twins and GoEs (non-guaranteed). |
| [`search.test.frg`](search.test.frg)                       | Tests predicates used for searching.        |
| [`to-board.sh`](to-board.sh)                               | Converts Evaluator set into a Forge syntactic set.        |

### Sigs

| Sig          | Purpose                                                                                                                                                                           |
| ------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `BoardState` | Represents state of the board, has a set of coordinates (Int->Int) that contain coordinates of cells that are alive in that state.                                                |
| `Board`      | Represents the board, has a firstState field which is the initial BoardState and next field that maps one BoardState to the next BoardState (mapping one generation to the next). |

### Predicates & Runs

#### Tracing

| Predicate    | Description                                              |
| ------------ | -------------------------------------------------------- |
| `wellformed` | Enforces general wellformedness on all traces.           |
| `trace`      | Enforces trace-specific behavior, such as initial state. |

| Run        | Description                                                                      |
| ---------- | -------------------------------------------------------------------------------- |
| `r██Trace` | Runs a specific trace given a board size and number of states (length of trace). |

#### Properties

| Predicate               | Description                                       |
| ----------------------- | ------------------------------------------------- |
| `isNotAdditive`         | Checks if a certain rule is not additive.         |
| `isNotInjective`        | Checks if a certain rule is not injective.        |
| `isNotMonotonic`        | Checks if a certain rule is not monotonic.        |
| `isNotNumberConserving` | Checks if a certain rule is not number conserving |

| Run                                | Description                                        |
| ---------------------------------- | -------------------------------------------------- |
| `counterexample_additive`          | Generates a counterexample of additivity.          |
| `injectivity_counterexample`       | Generates a counterexample of injectivity.         |
| `monotonic_counterexample`         | Generates a counterexample of montonicity.         |
| `number_conserving_counterexample` | Generates a counterexample of number conservation. |

#### Gardens of Eden

These are all in [`search.frg`](search.frg). Because of how Forge works, to run one of the asserts, comment out all asserts before it.

| Predicate              | Description                                      |
| ---------------------- | ------------------------------------------------ |
| `notTranslationOf`     | Prevents translations of a state from appearing. |
| `r██_excludedPatterns` | Prevents certain patterns/states from appearing. |

| Run                                | Description                                                                                    |
| ---------------------------------- | ---------------------------------------------------------------------------------------------- |
| `rule██GoE`                        | Generates a possible candidate GoE. See limitations below.                                     |
| `rule██GoE_blockedList`            | Generates a possible candidate GoE, given a list of prohibited states we don't want generated. |
| `verifyGoE`                        | Verifies a GoE based on a state and rule. Is guaranteed sound and tractable.                   |
| `number_conserving_counterexample` | Generates a counterexample of number conservation.                                             |

#### Twin

These are split between in [`cellular-automata.frg`](cellular-automata.frg) and [`search.frg`](search.frg). Because of how Forge works, to run one of the asserts, comment out all asserts before it.

| Predicate           | Description                                                                                                           |
| ------------------- | --------------------------------------------------------------------------------------------------------------------- |
| `weak_twins_rule██` | Describes what it measn for "weak" twins to exist -- essentially, the pre-images 2 for some state is at least size 2. |
| `strong_twin_r██`   | Describes what it measn for "strong" twins to exist.                                                                  |

| Run                | Description                                                                           |
| ------------------ | ------------------------------------------------------------------------------------- |
| `r██_findWeakTwin` | Soundly find two weak twins for a given rule.                                         |
| `r██_findTwin`     | Finds a candidate strong twin pair. Unsound due to limitations.                       |
| `r██_verifyTwin`   | Attempts to verify that a pair of twins are indeed twins. Unsound due to limitations. |

### Design "Aha!" Moments

Initially we set up our predicates to look for configurations that cannot have predecessors. But, because Forge is only looking in the given number of `BoardState`s, we were not getting reliable results. For example, forge could be given 8 `BoardState`s to look at and it might think it found a GoE because it found a set of 7 `BoardState`s that cannot be the predecessor to the remaining `BoardState`, but not necessarily because it had explored every single possible `BoardState`s that could be the predecessor to the supposed GoE.

We shifted our approach from finding GoEs to instead focusing on verifying them through testing known GoEs along with GoEs that our model found. Verifying known GoEs is a tractable problem that Forge is able to solve soundly. This is because it fixes the board we're verifying, and looking for a `BoardState` that could have formed the fixed state.

### Visualization

A [visualizer](visualizer.js) is included with this project, generated with the help of Claude.

> [!CAUTION]
> A visualizer is provided, but it should **only be used for tracing and generated Garden of Edens.** The visualizer is not intended to visualize generated candidates for twins. We recommend using the Evaluator and the verification systems in [search.frg](search.frg) and [cellular-automata.test.frg](cellular-automata.test.frg) with the associated [to-board.sh](to-board.sh) file to verify and examine Forge-generated candidates, even for Garden of Edens.

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
