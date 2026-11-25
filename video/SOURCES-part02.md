# Part Two: sources, checked artifacts, and scope

The episode builds from exact rational calculations to the interval kernel
in [acl2/interval-search.lisp](../acl2/interval-search.lisp). Its five
definitions are copied verbatim into the isolated
[teaching book](teaching-part02.lisp): `lw-intervalp`, `lw-contains`,
`lw-interval-add`, `lw-interval-sub`, and `lw-interval-scale`.
The full definitions appear before their compact call badges.

## Exact arithmetic and representation

The official [Numbers in ACL2](https://www.cs.utexas.edu/~moore/acl2/v2-4/acl2-doc-49.html)
describes integers and rational literals. The
[programming reference](https://www.cs.utexas.edu/~moore/acl2/v2-6/PROGRAMMING.html)
describes numerator and denominator in lowest terms. The teaching book
checks the rational equalities used in the film, including the error in
truncating one third to `333/1000`.

The official [ordered-pair documentation](https://www.cs.utexas.edu/~moore/acl2/v2-9/ACL2_Conses_or_Ordered_Pairs.html)
explains `cons`, `car`, `cdr`, and `consp`. An interval here is the dotted
pair `(lower . upper)`, not a proper list with two elements. `rationalp`
recognizes the endpoint and value domain. These are ordinary ACL2 rational
statements, not ACL2(r) statements about arbitrary reals.

The natural-number encoding discussion is illustrative: signed integers and
fractions have finite representations, and rational comparisons can be
cleared of positive denominators. This is not a certified full interpretation
of ACL2 in Peano Arithmetic.

The terminating decimals `1.001`, `1.003`, `1.999`, and `2.001` are display
notations for exact fractions, not ACL2 decimal literals. Actual calls use
`1001/1000`, `1003/1000`, `1999/1000`, and `2001/1000`.

## Eight independently certified theorems

The isolated book was certified using vanilla ACL2 8.5. Source, certificate
and compiled artifacts are under ignored `video/.tools/acl2-part02/`;
the log is `video/.tools/certify-part02.log`.

| Theorem | Guarantee |
| --- | --- |
| `lw-contains-add` | Endpoint addition preserves containment of the sum. |
| `lw-contains-sub` | Crossed endpoints preserve containment of the difference. |
| `lw-contains-scale` | Rational scaling with the sign branch preserves containment. |
| `lw-lower-gt-of-margin` | Containment, a width budget and a strict margin force the lower endpoint above the threshold. |
| `video-rational-sum-example` | One third plus one sixth is exactly one half. |
| `video-interval-add-width` | Addition adds interval widths. |
| `video-interval-sub-width` | Subtraction adds interval widths. |
| `video-positive-lower-sound` | A positive lower endpoint implies a positive contained value. |

The four `lw-*` theorem statements match the project kernel. The teaching
copy uses `:rule-classes nil` so these presentations install no rewrite
rules. The original nonlinear-arithmetic hint for scaling is retained.
There are no `skip-proofs`, trust tags, or admitted axioms in this book.
Assertions check the concrete interval examples and both precision choices
for `2x - y`. These teaching results are separate from the project count.

## Width, radius, and interpretation

Width is `upper - lower`. A symmetric error radius is half that width.
The composition example uses input radii `1/100` and then `1/1000`;
the strict-margin theorem uses a bound on full interval width.
Narrowing an interval requires a new enclosure justification.

The square-root example certifies the integer inequalities
`7*7 < 2*5*5` and `2*2*2 < 3*3`. Interpreting these as
`7/5 < sqrt(2) < 3/2` additionally uses positive square root and order
preservation of squaring on positive reals. That interpretation is explained
mathematically; it is not a teaching-book theorem about an irrational object.

The [arithmetic contract](../docs/arithmetic-contract.md) documents the
project's rational constructions and explicit interpretation theorems.
This episode claims neither the full Landau theorem nor a completed
Peano Arithmetic interpretation of it.
