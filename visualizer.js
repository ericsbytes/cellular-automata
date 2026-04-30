const d3 = require('d3')

/*
  Spacetime visualizer for OneDrule30 in game-of-life.frg.
  Rows = time steps (t=0 at top), columns = cell positions (0..13).
*/

const COLS = 14
const CELL = 32
const PAD = 20
const LABEL_W = 60

// ---------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------
function atomId(a) {
    return (a && typeof a.id === 'function') ? a.id() : String(a)
}

function getTuples(rel) {
    if (!rel) return []
    if (typeof rel.tuples === 'function') return rel.tuples()
    if (Array.isArray(rel)) return rel
    return []
}

function tupleAtoms(tup) {
    if (typeof tup.atoms === 'function') return tup.atoms()
    if (Array.isArray(tup)) return tup
    return [tup]
}

// Try multiple ways to get a field off a sig object
function getField(sigObj, name) {
    if (!sigObj) return null
    // Direct property (some Sterling versions expose fields this way)
    try { if (sigObj[name] != null) return sigObj[name] } catch (e) {}
    // .field() method
    try { return sigObj.field(name) } catch (e) {}
    return null
}

// ---------------------------------------------------------------
// Build alive map: stateAtomId -> Set<col>
// ---------------------------------------------------------------
function buildAliveMap() {
    const map = new Map()
    const rel = getField(BoardState, 'alive')
    for (const tup of getTuples(rel)) {
        const atoms = tupleAtoms(tup)
        if (atoms.length < 2) continue
        const sid = atomId(atoms[0])
        const c = parseInt(atomId(atoms[atoms.length - 1]), 10)
        if (!map.has(sid)) map.set(sid, new Set())
        if (!Number.isNaN(c)) map.get(sid).add(c)
    }
    return map
}

// ---------------------------------------------------------------
// Build next map: fromStateId -> toStateId
// Board.next is pfunc BoardState -> BoardState (tuples are Board×from×to or from×to)
// ---------------------------------------------------------------
function buildNextMap() {
    const map = new Map()
    const rel = getField(Board, 'next')
    for (const tup of getTuples(rel)) {
        const atoms = tupleAtoms(tup)
        if (atoms.length < 2) continue
        const from = atomId(atoms[atoms.length - 2])
        const to   = atomId(atoms[atoms.length - 1])
        map.set(from, to)
    }
    return map
}

// ---------------------------------------------------------------
// Get firstState atom id
// ---------------------------------------------------------------
function getFirstStateId() {
    const rel = getField(Board, 'firstState')
    for (const tup of getTuples(rel)) {
        const atoms = tupleAtoms(tup)
        if (atoms.length >= 1) return atomId(atoms[atoms.length - 1])
    }
    return null
}

// ---------------------------------------------------------------
// Return ordered list of alive-column Sets, one per time step.
// ---------------------------------------------------------------
function getOrderedStates() {
    // Strategy A: temporal instances[] API
    try {
        if (typeof instances !== 'undefined' && instances && instances.length > 1) {
            return instances.map(inst => {
                const cols = new Set()
                for (const tup of getTuples(getField(inst, 'alive') || inst.field('alive'))) {
                    const atoms = tupleAtoms(tup)
                    const c = parseInt(atomId(atoms[atoms.length - 1]), 10)
                    if (!Number.isNaN(c)) cols.add(c)
                }
                return cols
            })
        }
    } catch (e) { /* fall through */ }

    const aliveMap  = buildAliveMap()
    const nextMap   = buildNextMap()
    const firstId   = getFirstStateId()

    // Strategy B: walk firstState -> next chain
    if (firstId !== null && nextMap.size > 0) {
        const ordered = []
        let cur = firstId
        const visited = new Set()
        while (cur && !visited.has(cur)) {
            visited.add(cur)
            ordered.push(aliveMap.get(cur) || new Set())
            cur = nextMap.get(cur) || null
        }
        if (ordered.length > 1) return ordered
    }

    // Strategy C: sort atom IDs numerically (Forge names them BoardState0…N)
    // This preserves creation order, which matches the chain order.
    if (aliveMap.size > 1) {
        const sorted = [...aliveMap.keys()].sort((a, b) => {
            const na = parseInt(a.replace(/\D+/g, ''), 10)
            const nb = parseInt(b.replace(/\D+/g, ''), 10)
            return na - nb
        })
        // If we know firstId, rotate so it comes first
        if (firstId) {
            const fi = sorted.indexOf(firstId)
            if (fi > 0) sorted.push(...sorted.splice(0, fi))
        }
        return sorted.map(id => aliveMap.get(id))
    }

    // Strategy D: flat fallback — single state from all alive tuples
    const cols = new Set()
    for (const set of aliveMap.values()) set.forEach(c => cols.add(c))
    return [cols.size > 0 ? cols : new Set()]
}

// ---------------------------------------------------------------
// Render
// ---------------------------------------------------------------
d3.selectAll('svg > *').remove()

const states = getOrderedStates()
const ROWS = states.length

const root = d3.select(svg)

// Title
root.append('text')
    .attr('x', PAD + LABEL_W + (COLS * CELL) / 2)
    .attr('y', PAD + 16)
    .attr('text-anchor', 'middle')
    .style('font-size', '14px')
    .style('font-weight', 'bold')
    .style('fill', '#222')
    .text('Rule 30 — Spacetime Diagram')

const gGrid = root.append('g')
    .attr('transform', `translate(${PAD + LABEL_W}, ${PAD + 30})`)

// Column index labels
for (let c = 0; c < COLS; c++) {
    gGrid.append('text')
        .attr('x', c * CELL + CELL / 2)
        .attr('y', -4)
        .attr('text-anchor', 'middle')
        .style('font-size', '9px')
        .style('fill', '#888')
        .text(c)
}

// Cells
for (let t = 0; t < ROWS; t++) {
    const aliveCols = states[t]

    root.append('text')
        .attr('x', PAD + LABEL_W - 6)
        .attr('y', PAD + 30 + t * CELL + CELL / 2 + 4)
        .attr('text-anchor', 'end')
        .style('font-size', '11px')
        .style('fill', '#555')
        .text(`t=${t}`)

    for (let c = 0; c < COLS; c++) {
        gGrid.append('rect')
            .attr('x', c * CELL)
            .attr('y', t * CELL)
            .attr('width',  CELL)
            .attr('height', CELL)
            .attr('fill', aliveCols.has(c) ? '#1a1a2e' : '#f0f0f0')
            .attr('stroke', '#ccc')
            .attr('stroke-width', 0.5)
    }
}

// Footer
root.append('text')
    .attr('x', PAD + LABEL_W)
    .attr('y', PAD + 30 + ROWS * CELL + 16)
    .style('font-size', '11px')
    .style('fill', '#666')
    .text(`${ROWS} time steps · ${COLS} cells · Rule 30`)
