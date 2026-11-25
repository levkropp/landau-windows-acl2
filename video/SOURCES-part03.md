# Part Three: sources, checked artifacts, and scope

The [teaching book](teaching-part03.lisp) combines isolated copies of
[interval-search.lisp](../acl2/interval-search.lisp) and
[grid-witness.lisp](../acl2/grid-witness.lisp), retaining their definitions,
theorem statements and proof hints. The second book's `include-book` is
replaced by the first book's actual forms in this standalone copy.
Three additional teaching theorems justify a simple uniform-grid constructor.

## Checked content

The book certifies **18 theorems** with vanilla ACL2 8.5: the 15 project
theorems in those snapshots and three constructor lemmas (length, first
address, and mesh validity). It contains 15 function definitions, including
five interval functions already introduced in Part Two and the new teaching
constructor. No `skip-proofs`, trust tags, or admitted axioms are used.

The certificate and identical source copy are under ignored
`video/.tools/acl2-part03/`; the log is `video/.tools/certify-part03.log`.
These are independent teaching certificates, separate from project counts.

| Result | Meaning |
| --- | --- |
| `lw-first-above-index-natural`, `lw-first-above-index-bound` | A successful result has an index within the sample list. |
| `lw-first-above-nth` | The returned interval is the indexed sample. |
| `lw-first-above-value-gt` | Correct input enclosures turn a returned interval into a value above the threshold. |
| `lw-first-above-complete` | Search succeeds iff some stored lower endpoint passes the test. |
| `lw-search-complete-of-margin` | A sufficiently large sampled value and sufficiently narrow enclosures force search success. |
| `lw-mesh-covers-point` | Sorted bounded gaps cover rational points inside the grid span. |
| `lw-margin-survives-transport`, `lw-nearby-forces-large-value` | The supplied rate bound transports a strict peak margin to a nearby sample. |
| `lw-grid-search-complete` | Coverage, lower transport, enclosure accuracy, and the strict margin force a successful finite scan. |
| `video-uniform-grid-*` | The teaching constructor has the requested length and starting address, and satisfies the mesh predicate under its domain hypotheses. |

All ten custom functions newly used on screen are shown completely before
compact use. Long definitions and the final theorem appear across numbered
source cards. Display line wrapping only changes whitespace; the teaching
book retains the original project definitions verbatim.

## One worked example

The illustrated function is `F(x) = 1 - 4*abs(x - 7/16)` on `[0,1]`.
The grid is `0, 1/8, ..., 1`; each interval has radius `1/8` around its
exact teaching value, hence full width `1/4`.

The point is `7/16`, peak `1`, rate `4`, mesh `1/8`, threshold `0`, and
width budget `1/4`. The strict margin is `1 > 0 + 4*(1/8) + 1/4 = 3/4`.
The first successful index is `2`, whose address is `1/4` and whose interval
is `(1/8 . 3/8)`. This is not the closest sample to the peak; the algorithm
returns the first qualifying interval in list order.

Assertions check the complete numerical premises and returned result,
the coarse endpoint-only failure, and a positive value hidden by an
insufficiently narrow enclosure. The curve is an explicit teaching example,
not a computed Landau-statistic plot. The book checks the finite list's
lower transport inequalities; it does not introduce a general analytic
function and certify a global Lipschitz theorem for it.

## Language and scope

The official [Gentle Introduction to ACL2 Programming](https://www.cs.utexas.edu/~moore/publications/gentle-intro-to-acl2-programming.html)
explains list accessors, zero-based `nth`, and `endp`. The
[A Little Logic course notes](https://www.cs.utexas.edu/~moore/publications/cs313k.pdf)
explain that `nil` alone is false; zero is not false. The lesson uses proper
finite lists. `endp` is described in that domain, not as a general
proper-list recognizer. The `zp` base case is used with a natural count;
see the official [zero-test documentation](https://www.cs.utexas.edu/~moore/acl2/v2-8/ZERO-TEST-IDIOMS.html).

`video-uniform-grid` is a teaching constructor. The project window grid
has additional rational endpoint and coverage obligations. The full
success theorem shown here is conditional and rational: the evaluator must
provide the enclosure premise and mathematical lower transport bounds.
Termination alone establishes neither those premises nor a successful result.

Relating the arithmetic construction to the actual analytic signal remains
an explicit interpretation obligation. This episode claims neither the
full Landau result nor a completed interpretation of ACL2 in Peano Arithmetic.
