const d3 = require('d3')

/*
  Visualizer for game-of-life.frg.
  Works for both 1D automata (Rule 30, Rule 90) and 2D Game of Life.

  Sterling exposes sig names and field names as global Relation objects:
    alive       : BoardState -> Int -> Int   (arity 3)
    next        : Board -> BoardState -> BoardState  (arity 3)
    firstState  : Board -> BoardState        (arity 2)

  Each Relation has .tuples() -> Tuple[], each Tuple has .atoms() -> Atom[],
  each Atom has .id() -> string. For Int atoms, id() is the integer as a string.
*/

const CELL = 28
const PAD  = 20
const LABEL_W = 48

// ---------------------------------------------------------------------------
// Utilities
// ---------------------------------------------------------------------------

function atomId(a) {
    try { if (typeof a.id === 'function') return a.id() } catch (e) {}
    return String(a)
}

function getTuples(rel) {
    if (!rel) return []
    try { if (typeof rel.tuples === 'function') return rel.tuples() } catch (e) {}
    if (Array.isArray(rel)) return rel
    return []
}

function tupleAtoms(tup) {
    try { if (typeof tup.atoms === 'function') return tup.atoms() } catch (e) {}
    if (Array.isArray(tup)) return tup
    return [tup]
}

// Try to get a named relation: prefer a global variable, fall back to property / method on obj
function getRelation(globalName, fallbackObj) {
    try {
        const g = eval(globalName) // eslint-disable-line no-eval
        if (g != null && (typeof g.tuples === 'function' || Array.isArray(g))) return g
    } catch (e) {}
    if (!fallbackObj) return null
    try { if (fallbackObj[globalName] != null) return fallbackObj[globalName] } catch (e) {}
    try { return fallbackObj.field(globalName) } catch (e) {}
    return null
}

// ---------------------------------------------------------------------------
// Build alive map:  stateAtomId -> Set< "row,col" >
// alive is a ternary relation: BoardState -> Int -> Int
// ---------------------------------------------------------------------------
function buildAliveMap() {
    const map = new Map()
    // Try the global `alive` relation first, then fall back to BoardState.alive
    const fallback = (() => { try { return eval('BoardState') } catch(e) { return null } })() // eslint-disable-line no-eval
    const rel = getRelation('alive', fallback)

    for (const tup of getTuples(rel)) {
        const atoms = tupleAtoms(tup)
        // Expect (BoardState_atom, row_Int, col_Int) — arity 3
        // If only 2 atoms, treat as (row_Int, col_Int) belonging to a shared state "default"
        if (atoms.length === 0) continue
        let sid, rAtom, cAtom
        if (atoms.length >= 3) {
            sid   = atomId(atoms[0])
            rAtom = atoms[1]
            cAtom = atoms[2]
        } else if (atoms.length === 2) {
            sid   = 'default'
            rAtom = atoms[0]
            cAtom = atoms[1]
        } else {
            continue
        }
        const r = parseInt(atomId(rAtom), 10)
        const c = parseInt(atomId(cAtom), 10)
        if (isNaN(r) || isNaN(c)) continue
        if (!map.has(sid)) map.set(sid, new Set())
        map.get(sid).add(`${r},${c}`)
    }
    return map
}

// ---------------------------------------------------------------------------
// Build next map:  fromStateId -> toStateId
// next is ternary: Board -> BoardState -> BoardState
// ---------------------------------------------------------------------------
function buildNextMap() {
    const map = new Map()
    const fallback = (() => { try { return eval('Board') } catch(e) { return null } })() // eslint-disable-line no-eval
    const rel = getRelation('next', fallback)

    for (const tup of getTuples(rel)) {
        const atoms = tupleAtoms(tup)
        // Expect (Board_atom, from, to) — arity 3; or (from, to) — arity 2
        if (atoms.length < 2) continue
        const from = atomId(atoms[atoms.length - 2])
        const to   = atomId(atoms[atoms.length - 1])
        // Avoid self-loops (shouldn't happen, but be safe)
        if (from !== to) map.set(from, to)
    }
    return map
}

// ---------------------------------------------------------------------------
// Get firstState atom id
// firstState is binary: Board -> BoardState
// ---------------------------------------------------------------------------
function getFirstStateId() {
    const fallback = (() => { try { return eval('Board') } catch(e) { return null } })() // eslint-disable-line no-eval
    const rel = getRelation('firstState', fallback)

    for (const tup of getTuples(rel)) {
        const atoms = tupleAtoms(tup)
        if (atoms.length >= 1) return atomId(atoms[atoms.length - 1])
    }
    return null
}

// ---------------------------------------------------------------------------
// Return ordered array of alive-Sets, one per time step
// ---------------------------------------------------------------------------
function getOrderedStates() {
    const aliveMap = buildAliveMap()
    const nextMap  = buildNextMap()
    const firstId  = getFirstStateId()

    // Walk firstState -> next -> next ...
    if (firstId !== null) {
        const ordered = []
        let cur = firstId
        const visited = new Set()
        while (cur && !visited.has(cur)) {
            visited.add(cur)
            ordered.push(aliveMap.get(cur) || new Set())
            cur = nextMap.get(cur) || null
        }
        if (ordered.length > 0) return ordered
    }

    // Fallback: sort by numeric suffix (Forge names atoms BoardState0 … BoardStateN)
    const sorted = [...aliveMap.keys()].sort((a, b) => {
        const na = parseInt(a.replace(/\D+/g, ''), 10)
        const nb = parseInt(b.replace(/\D+/g, ''), 10)
        return na - nb
    })
    if (firstId) {
        const fi = sorted.indexOf(firstId)
        if (fi > 0) sorted.push(...sorted.splice(0, fi))
    }
    return sorted.map(id => aliveMap.get(id) || new Set())
}

// ---------------------------------------------------------------------------
// Detect grid bounds from all alive cells across all states.
// Always anchors at 0 and pads to show dead cells around alive ones.
// ---------------------------------------------------------------------------
function getGridDims(states) {
    let minR = Infinity, maxR = -Infinity
    let minC = Infinity, maxC = -Infinity
    let any = false
    for (const s of states) {
        for (const key of s) {
            const [r, c] = key.split(',').map(Number)
            any = true
            if (r < minR) minR = r; if (r > maxR) maxR = r
            if (c < minC) minC = c; if (c > maxC) maxC = c
        }
    }
    if (!any) return { minR: 0, maxR: 0, minC: 0, maxC: 13, is1D: true }

    const is1D = (minR === maxR)

    if (is1D) {
        // Anchor at column 0 and ensure at least 14 columns are visible so
        // dead/empty cells around the alive region are always shown.
        minC = Math.min(0, minC)
        maxC = Math.max(maxC, minC + 13)
    } else {
        // For 2D, anchor at (0,0) and ensure at least an 8x8 display area.
        minR = Math.min(0, minR)
        minC = Math.min(0, minC)
        maxR = Math.max(maxR, minR + 7)
        maxC = Math.max(maxC, minC + 7)
    }

    return { minR, maxR, minC, maxC, is1D }
}

// ---------------------------------------------------------------------------
// Render
// ---------------------------------------------------------------------------
d3.selectAll('svg > *').remove()
const root = d3.select(svg)

const states = getOrderedStates()
const ROWS   = states.length

// Nothing to show
if (ROWS === 0 || states.every(s => s.size === 0)) {
    root.append('text').attr('x', 20).attr('y', 30)
        .style('font-size', '12px').style('fill', 'red')
        .text('No alive cells found. Ensure the run has a sat result.')
} else {
    const { minR, maxR, minC, maxC, is1D } = getGridDims(states)
    const COLS      = maxC - minC + 1
    const GRID_ROWS = maxR - minR + 1

    if (is1D) {
        // ---- Spacetime diagram (1D automaton) ----
        root.append('text')
            .attr('x', PAD + LABEL_W + (COLS * CELL) / 2).attr('y', PAD + 14)
            .attr('text-anchor', 'middle')
            .style('font-size', '14px').style('font-weight', 'bold').style('fill', '#222')
            .text('Rule 30 — Spacetime Diagram')

        const gGrid = root.append('g')
            .attr('transform', `translate(${PAD + LABEL_W}, ${PAD + 28})`)

        // Column index labels
        for (let ci = 0; ci < COLS; ci++) {
            gGrid.append('text')
                .attr('x', ci * CELL + CELL / 2).attr('y', -3)
                .attr('text-anchor', 'middle')
                .style('font-size', '9px').style('fill', '#888')
                .text(ci + minC)
        }

        for (let t = 0; t < ROWS; t++) {
            const aliveCells = states[t]

            // Row label
            root.append('text')
                .attr('x', PAD + LABEL_W - 4)
                .attr('y', PAD + 28 + t * CELL + CELL / 2 + 4)
                .attr('text-anchor', 'end')
                .style('font-size', '10px').style('fill', '#555')
                .text(`t=${t}`)

            for (let ci = 0; ci < COLS; ci++) {
                const c = ci + minC
                const alive = aliveCells.has(`${minR},${c}`)
                gGrid.append('rect')
                    .attr('x', ci * CELL).attr('y', t * CELL)
                    .attr('width', CELL).attr('height', CELL)
                    .attr('fill', alive ? '#1a1a2e' : '#f0f0f0')
                    .attr('stroke', '#ccc').attr('stroke-width', 0.5)
            }
        }

        root.append('text')
            .attr('x', PAD + LABEL_W)
            .attr('y', PAD + 28 + ROWS * CELL + 16)
            .style('font-size', '11px').style('fill', '#666')
            .text(`${ROWS} time steps · col ${minC}..${maxC}`)

    } else {
        // ---- 2D Game of Life: states shown side by side ----
        const stateW = COLS * CELL + 12

        root.append('text')
            .attr('x', PAD + (ROWS * stateW) / 2).attr('y', PAD + 14)
            .attr('text-anchor', 'middle')
            .style('font-size', '14px').style('font-weight', 'bold').style('fill', '#222')
            .text('Game of Life')

        for (let t = 0; t < ROWS; t++) {
            const aliveCells = states[t]
            const g = root.append('g')
                .attr('transform', `translate(${PAD + t * stateW}, ${PAD + 28})`)

            g.append('text')
                .attr('x', COLS * CELL / 2).attr('y', -3)
                .attr('text-anchor', 'middle')
                .style('font-size', '10px').style('fill', '#555')
                .text(`t=${t}`)

            for (let ri = 0; ri < GRID_ROWS; ri++) {
                for (let ci = 0; ci < COLS; ci++) {
                    const r = ri + minR
                    const c = ci + minC
                    const alive = aliveCells.has(`${r},${c}`)
                    g.append('rect')
                        .attr('x', ci * CELL).attr('y', ri * CELL)
                        .attr('width', CELL).attr('height', CELL)
                        .attr('fill', alive ? '#1a1a2e' : '#f0f0f0')
                        .attr('stroke', '#ccc').attr('stroke-width', 0.5)
                }
            }
        }

        root.append('text')
            .attr('x', PAD)
            .attr('y', PAD + 28 + GRID_ROWS * CELL + 16)
            .style('font-size', '11px').style('fill', '#666')
            .text(`${ROWS} states · rows ${minR}..${maxR} · cols ${minC}..${maxC}`)
    }
}
