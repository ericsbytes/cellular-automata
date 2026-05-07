#lang forge

option run_sterling "visualizer.js"

sig BoardState {
    alive: set Int->Int
}

one sig Board {
    firstState: one BoardState,
    next: pfunc BoardState -> BoardState
}

--========================================================--
--  SETUP PREDICATES                                      --
--========================================================--

pred wellformed {
    // first state cannot be next of some other state
    Board.firstState not in BoardState.(Board.next)

    // last state is the only one without a next state
    one lastState: BoardState | no Board.next[lastState]

    // states are linear
    no s: BoardState | s in s.^(Board.next)

    // all states should be connected
    Board.firstState.*(Board.next) = BoardState

    // one dimensional
    board1D
}

assert wellformed is sat

pred board1D {
    all s: BoardState | {
        all r, c: Int | (r->c) in s.alive implies {
            r = 0
        }
    }
}

pred board2D[rowSize, colSize: Int] {
    all s: BoardState | {
        all r, c: Int | (r->c) in s.alive implies {
            r < rowSize
            c < colSize
        }
    }
}

// Helper function to get left and right neighbors
fun left[c: Int]: Int { add[c, -1] }
fun right[c: Int]: Int { add[c,  1] }

// Helper functions to get the state of the three cells in a neighborhood
pred leftState[pre: BoardState, c: Int] { (0->left[c]) in pre.alive }
pred centerState[pre: BoardState, c: Int] { (0->c) in pre.alive }
pred rightState[pre: BoardState, c: Int] { (0->right[c]) in pre.alive }

--========================================================--
--  RULES                                                 --
--========================================================--

fun rule30next[pre: BoardState]: set Int->Int {
    { 
        r: Int, c: Int | r = 0 and (
            (leftState[pre, c] and not centerState[pre, c] and not rightState[pre, c]) or  // 100
            (not leftState[pre, c] and centerState[pre, c] and rightState[pre, c]) or      // 011
            (not leftState[pre, c] and centerState[pre, c] and not rightState[pre, c]) or  // 010
            (not leftState[pre, c] and not centerState[pre, c] and rightState[pre, c])     // 001
        )
    }
}

pred rule30step[pre, post: BoardState] {
    post.alive = rule30next[pre]
}

fun rule90next[pre: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            (leftState[pre, c] and centerState[pre, c] and not rightState[pre, c]) or     // 110
            (leftState[pre, c] and not centerState[pre, c] and not rightState[pre, c]) or // 100
            (not leftState[pre, c] and centerState[pre, c] and rightState[pre, c]) or     // 011
            (not leftState[pre, c] and not centerState[pre, c] and rightState[pre, c])    // 001
        )
    }
}

pred rule90step[pre, post: BoardState] {
    post.alive = rule90next[pre]
}

fun rule110next[pre: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            (leftState[pre, c] and centerState[pre, c] and not rightState[pre, c]) or     // 110
            (leftState[pre, c] and not centerState[pre, c] and rightState[pre, c]) or     // 101
            (not leftState[pre, c] and centerState[pre, c] and rightState[pre, c]) or     // 011
            (not leftState[pre, c] and centerState[pre, c] and not rightState[pre, c]) or // 010
            (not leftState[pre, c] and not centerState[pre, c] and rightState[pre, c])    // 001
        )
    }
}


pred rule110step[pre, post: BoardState] {
    post.alive = rule110next[pre]
}

// RULE 60: Pascal's triangle modulo 2 (XOR with left neighbor only)
fun rule60next[pre: BoardState]: set Int->Int {
    { r: Int, c: Int | r = 0 and 
        (leftState[pre, c] xor centerState[pre, c])
    }
}

pred rule60step[pre, post: BoardState] {
    post.alive = rule60next[pre]
}

// RULE 102: Right-triangular rule (XOR with right neighbor only)
fun rule102next[pre: BoardState]: set Int->Int {
    { r: Int, c: Int | r = 0 and 
        (centerState[pre, c] xor rightState[pre, c])
    }
}

pred rule102step[pre, post: BoardState] {
    post.alive = rule102next[pre]
}

fun rule170next[pre: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            // Cases where left neighbor is alive (1)
            (leftState[pre, c] and centerState[pre, c] and rightState[pre, c]) or     // 111
            (leftState[pre, c] and centerState[pre, c] and not rightState[pre, c]) or // 110
            (leftState[pre, c] and not centerState[pre, c] and rightState[pre, c]) or // 101
            (leftState[pre, c] and not centerState[pre, c] and not rightState[pre, c])    // 100
        )
    }
}

pred rule170step[pre, post: BoardState] {
    post.alive = rule170next[pre]
}

fun rule184next[pre: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            (leftState[pre, c] and centerState[pre, c] and rightState[pre, c]) or     // 111 → 1
            (leftState[pre, c] and not centerState[pre, c] and rightState[pre, c]) or // 101 → 1
            (leftState[pre, c] and not centerState[pre, c] and not rightState[pre, c]) or // 100 → 1
            (not leftState[pre, c] and centerState[pre, c] and rightState[pre, c])    // 011 → 1
        )
    }
}

pred rule184step[pre, post: BoardState] {
    post.alive = rule184next[pre]
}

// Rule 73 
fun rule73next[pre: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            (leftState[pre, c] and centerState[pre, c] and not rightState[pre, c]) or     // 110 → 1
            (not leftState[pre, c] and centerState[pre, c] and rightState[pre, c]) or     // 011 → 1
            (not leftState[pre, c] and not centerState[pre, c] and not rightState[pre, c])    // 000 → 1
        )
    }
}

pred rule73step[pre, post: BoardState] {
    post.alive = rule73next[pre]
}

// Rule 45
fun rule45next[pre: BoardState]: set Int->Int {
    {
        r: Int, c: Int | r = 0 and (
            (leftState[pre, c] and not centerState[pre, c] and rightState[pre, c]) or     // 101 → 1
            (not leftState[pre, c] and centerState[pre, c] and rightState[pre, c]) or     // 011 → 1
            (not leftState[pre, c] and centerState[pre, c] and not rightState[pre, c]) or // 010 → 1
            (not leftState[pre, c] and not centerState[pre, c] and not rightState[pre, c])    // 000 → 1
        )
    }
}

pred rule45step[pre, post: BoardState] {
    post.alive = rule45next[pre]
}

--========================================================--
--  TRACES                                                --
--========================================================--

// gives a trace that starts from a single cell at (0, 0)
pred trace {
    wellformed
    Board.firstState.alive = 0->0
    all r, c: Int | {
        c != 0 implies (r->c) not in Board.firstState.alive
    } 
}

r30Trace: run {
    all s: BoardState | some Board.next[s] implies rule30step[s,  Board.next[s]]
    trace
} for exactly 8 BoardState, 5 Int

r90Trace: run {
    all s: BoardState | some Board.next[s] implies rule90step[s,  Board.next[s]]
    trace
} for exactly 12 BoardState, 5 Int 

r110Trace: run {
    all s: BoardState | some Board.next[s] implies rule110step[s,  Board.next[s]]
    trace
} for exactly 12 BoardState, 5 Int

r184Trace: run {
    all s: BoardState | some Board.next[s] implies rule184step[s,  Board.next[s]]
    trace
} for exactly 12 BoardState, 5 Int

r73Trace: run {
    all s: BoardState | some Board.next[s] implies rule73step[s,  Board.next[s]]
    trace
} for exactly 12 BoardState, 5 Int


--========================================================--
--  TWINS                                                 --
--========================================================--

pred weak_twins_rule30 {
    some disj s1, s2, r1, r2: BoardState | {
        rule30step[s1, r1]
        rule30step[s2, r2]
        s1.alive != s2.alive
        r1.alive = r2.alive
    }
}

pred weak_twins_rule60 {
    some disj s1, s2, r1, r2: BoardState | {
        rule60step[s1, r1]
        rule60step[s2, r2]
        s1.alive != s2.alive
        r1.alive = r2.alive
    }
}

pred strong_twin_r30[bs, other: BoardState] {
    all s1, s2: BoardState | {
        s2.alive = (s1.alive - bs.alive) + other.alive implies rule30next[s1] = rule30next[s2]
    }

    all s1, s2: BoardState | {
        s2.alive = (s1.alive - other.alive) + bs.alive implies rule30next[s1] = rule30next[s2]
    }
}

// NOTE: what is sound is finding "exact" twins
r30_findExactTwin: run {
    board1D
    some disj s1, s2: BoardState | {
        some s1.alive
        some s2.alive
        s1.alive != s2.alive
        rule30next[s1] = rule30next[s2]
    }
} for exactly 2 BoardState, 5 Int



--========================================================--
--  PROPERTY PREDICATES                                --
--========================================================--

// Checking  if the rule is additive by finding counterexaples if it isn't. 
// To check, fill in following predicate, then run the following
pred isNotAdditive {
    some disj s1, s2, sXOR, r1, r2, rXOR: BoardState | {
        sXOR.alive = (s1.alive - s2.alive) + (s2.alive - s1.alive)
        rule110step[s1, r1]
        rule110step[s2, r2]
        rule110step[sXOR, rXOR]
        rXOR.alive != (r1.alive - r2.alive) + (r2.alive - r1.alive)
    }
}

// If it is additive, counterexample_additive will be unsat.
counterexample_additive: run {
    board1D
    all c: Int, s: BoardState  | c < -4 or c >= 7 implies (0->c) not in s.alive
    isNotAdditive
} for exactly 6 BoardState, 4 Int


pred isNotInjective {
    some s1, s2, r1, r2: BoardState | {
        s1 != s2  // Different configurations
        rule110step[s1, r1]
        rule110step[s2, r2]
        r1.alive = r2.alive  

    }
}

injectivity_counterexample: run {
    board1D
    all c: Int, s: BoardState | c < -7 or c >= 6 implies (0->c) not in s.alive
    isNotInjective
} for exactly 4 BoardState, 4 Int


pred isNotMonotonic {
    some s1, s2, r1, r2: BoardState | {
        // s1 is subset of s2
        s1.alive in s2.alive
        
        rule60step[s1, r1]
        rule60step[s2, r2]
        
        // Monotonicity VIOLATED
        not (r1.alive in r2.alive)
    }
}

monotonic_counterexample: run {
    board1D
    all c: Int, s: BoardState | c < 0 or c >= 4 implies (0->c) not in s.alive
    isNotMonotonic
} for exactly 5 BoardState, 4 Int

pred isNotNumberConserving {
    some s, next: BoardState | {
        rule170step[s, next]
        #{c: Int | (0->c) in s.alive} != #{c: Int | (0->c) in next.alive}
    }
}

number_conserving_counterexample: run {
    board1D
    all c: Int, s: BoardState | c < 0 or c >= 4 implies (0->c) not in s.alive
    isNotNumberConserving
} for exactly 5 BoardState, 4 Int


--========================================================--
--  GARDENS OF EDENS                                      --
--========================================================--

/*
    NOTE: refactored. see search.frg
*/

// possible expansions
// - given a configuration, attempt to verify if it's orphan or not
// - attempt to verify twins <=> orphans
// - verify that when a rule is not supposed to have orphans, it doesn't generate orphans
// - find more orphans by restricting boring configurations
// - bijective <=> twins

// should be unsat!! but generates instances
// probable explanation is that rule 90 is surjective in infinite grids, but because
// it is limited to a wrap-around board, it may not be surjective anymore
