const d3 = require('d3')

/*
  Custom visualization for gameOfLife_inclass.frg.

  Pages through the states of a temporal trace and, for each state, shows a
  preview grid plus the RLE encoding suitable for pasting into Golly /
  LifeViewer / copy.sh/life.

  Coordinate mapping (bitwidth = 3 Int, so rows/cols span [-4, 3]):
	  Forge (r, c)  ->  RLE (x = c + 4, y = r + 4)
  This matches Golly's convention that a bounded w x h grid has top-left
  at (-int(w/2), -int(h/2)).
*/

const W = 8, H = 8

// ---------------------------------------------------------------
// Extract the alive set for every state in the trace.
// Each entry is a Set of "r,c" strings.
//
// NOTE FOR TIM: if Sterling-for-Forge's temporal API isn't what
// Attempt A guesses, adjust here (one place).
// ---------------------------------------------------------------
function getAllStates() {
	const out = []

	const parseAtom = (a) => {
		const s = (a && typeof a.id === 'function') ? a.id() : String(a)
		return parseInt(s, 10)
	}
	const tupleToRC = (tup) => {
		const atoms = (typeof tup.atoms === 'function') ? tup.atoms() : tup
		const r = parseAtom(atoms[atoms.length - 2])
		const c = parseAtom(atoms[atoms.length - 1])
		return Number.isNaN(r) || Number.isNaN(c) ? null : r + ',' + c
	}

	// Attempt A: `instances` array, per-state field access.
	try {
		if (typeof instances !== 'undefined' && instances && instances.length > 0) {
			for (const state of instances) {
				const set = new Set()
				const field = state.field('alive')
				const tuples = (typeof field.tuples === 'function') ? field.tuples() : field
				for (const tup of tuples) {
					const key = tupleToRC(tup)
					if (key !== null) set.add(key)
				}
				out.push(set)
			}
			return out
		}
	} catch (e) { /* fall through */ }

	// Attempt B: flat globals — only the current state is visible.
	try {
		const field = Board.alive || Board.field('alive')
		const tuples = (typeof field.tuples === 'function') ? field.tuples() : field
		const set = new Set()
		for (const tup of tuples) {
			const key = tupleToRC(tup)
			if (key !== null) set.add(key)
		}
		out.push(set)
	} catch (e) { /* give up */ }

	return out
}

// ---------------------------------------------------------------
// Grid + RLE encoding.
// ---------------------------------------------------------------
function buildGrid(aliveSet) {
	const grid = Array.from({ length: H }, () => Array(W).fill(false))
	for (const key of aliveSet) {
		const [r, c] = key.split(',').map(Number)
		const y = r + 4, x = c + 4
		if (y >= 0 && y < H && x >= 0 && x < W) grid[y][x] = true
	}
	return grid
}

function encodeRowTokens(row) {
	// Runs of identical cells. Run length 1 is implicit (just the letter).
	const runs = []
	let i = 0
	while (i < row.length) {
		let j = i
		while (j < row.length && row[j] === row[i]) j++
		runs.push({ len: j - i, alive: row[i] })
		i = j
	}
	// Trailing dead cells on a row are dropped (implicit before $ / !).
	if (runs.length && !runs[runs.length - 1].alive) runs.pop()
	return runs.map(r => (r.len === 1 ? '' : r.len) + (r.alive ? 'o' : 'b')).join('')
}

function encodeRLE(grid) {
	const rowTokens = grid.map(encodeRowTokens)

	// Emit `$` separators equal to the gap between the current row and the last
	// emitted row: N blank rows between two non-blank rows => (N+1)$ total.
	// Leading blank rows contribute to the gap from "row -1" too, so the first
	// non-empty row at index y emits `y$` before its content (0$ is nothing).
	let body = ''
	let prevY = -1
	for (let y = 0; y < rowTokens.length; y++) {
		if (rowTokens[y] === '') continue
		const gap = prevY < 0 ? y : (y - prevY)
		if (gap > 0) body += (gap === 1 ? '' : gap) + '$'
		body += rowTokens[y]
		prevY = y
	}
	body += '!'

	const header = `x = ${W}, y = ${H}, rule = B3/S23:T${W},${H}`
	return header + '\n' + body + '\n'
}

// ---------------------------------------------------------------
// Render: preview grid + RLE textarea + download/copy/prev/next.
// ---------------------------------------------------------------
d3.selectAll('svg > *').remove()

const states = getAllStates()
const nStates = states.length || 1
let curIdx = 0

const CELL = 18, PAD = 10
const gridOrigin = { x: PAD, y: PAD + 24 }

const root = d3.select(svg)

// Title + state counter (updated per page).
const title = root.append('text')
	.attr('x', PAD).attr('y', PAD + 14)
	.style('font-size', '13px').style('font-weight', 'bold').style('fill', '#222')

// Preview grid cells (created once, updated on paging).
const gPreview = root.append('g')
	.attr('transform', `translate(${gridOrigin.x},${gridOrigin.y})`)
const cellRects = []
for (let y = 0; y < H; y++) {
	const rowRects = []
	for (let x = 0; x < W; x++) {
		const rect = gPreview.append('rect')
			.attr('x', x * CELL).attr('y', y * CELL)
			.attr('width', CELL).attr('height', CELL)
			.attr('stroke', '#bbb').attr('stroke-width', 0.5)
		rowRects.push(rect)
	}
	cellRects.push(rowRects)
}

const footer = root.append('text')
	.attr('x', PAD).attr('y', gridOrigin.y + H * CELL + 16)
	.style('font-size', '12px').style('fill', '#555')

// HTML widgets (textarea + buttons) live in a foreignObject.
const foWidth = 380, foHeight = 260
const fo = root.append('foreignObject')
	.attr('x', gridOrigin.x + W * CELL + PAD * 2)
	.attr('y', PAD)
	.attr('width', foWidth)
	.attr('height', foHeight)

const container = fo.append('xhtml:div')
	.style('font-family', 'sans-serif')
	.style('font-size', '12px')

container.append('xhtml:div')
	.style('margin-bottom', '4px')
	.text('RLE for current state (paste into Golly / LifeViewer / copy.sh/life):')

const ta = container.append('xhtml:textarea')
	.attr('readonly', true)
	.style('width', (foWidth - 10) + 'px')
	.style('height', '110px')
	.style('font-family', 'monospace')
	.style('font-size', '11px')
	.style('box-sizing', 'border-box')

const btnRow = container.append('xhtml:div').style('margin-top', '6px')

const prevBtn = btnRow.append('xhtml:button').text('\u2190 Prev')
const nextBtn = btnRow.append('xhtml:button').text('Next \u2192').style('margin-left', '4px')

btnRow.append('xhtml:button')
	.style('margin-left', '12px')
	.text('Download .rle')
	.on('click', () => {
		const rle = encodeRLE(buildGrid(states[curIdx] || new Set()))
		const blob = new Blob([rle], { type: 'text/plain' })
		const url = URL.createObjectURL(blob)
		const a = document.createElement('a')
		a.href = url
		a.download = `forge-gol-state${curIdx}.rle`
		document.body.appendChild(a)
		a.click()
		document.body.removeChild(a)
		URL.revokeObjectURL(url)
	})

btnRow.append('xhtml:button')
	.style('margin-left', '4px')
	.text('Copy')
	.on('click', () => {
		const node = ta.node()
		node.select()
		try { document.execCommand('copy') } catch (e) { /* ignore */ }
	})

function render(idx) {
	curIdx = Math.max(0, Math.min(nStates - 1, idx))
	const aliveSet = states[curIdx] || new Set()
	const grid = buildGrid(aliveSet)
	const rle = encodeRLE(grid)

	title.text(`Game of Life  ·  state ${curIdx + 1} / ${nStates}`)
	footer.text(`${aliveSet.size} live cell(s)  ·  ${W}x${H} torus`)

	for (let y = 0; y < H; y++) {
		for (let x = 0; x < W; x++) {
			cellRects[y][x].attr('fill', grid[y][x] ? '#222' : '#f5f5f5')
		}
	}
	ta.node().value = rle

	prevBtn.attr('disabled', curIdx === 0 ? true : null)
	nextBtn.attr('disabled', curIdx === nStates - 1 ? true : null)
}

prevBtn.on('click', () => render(curIdx - 1))
nextBtn.on('click', () => render(curIdx + 1))

render(0)
