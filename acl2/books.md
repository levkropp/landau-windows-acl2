# Certified ACL2 books

The default certification path contains **647 books and 3,649 exported
theorems**. Counts include exported `defthm` events per book; local
proof-support lemmas are excluded. A shared theorem exported by two books
counts in each.
See [the ACL2 guide](README.md) for the current proof path, reproduction
commands and the remaining obligations for the full theorem.

| Book | General results |
|---|---|
| `interval-search.lisp` | Rational interval addition, subtraction and signed scaling; margin propagation; bounded-search completeness, soundness, and returned-index correctness |
| `grid-witness.lisp` | Coverage by a finite rational mesh; Lipschitz transport of a peak; guaranteed success of the interval search after accounting for transport and enclosure error |
| `rational-window.lisp` | Computed precision fuel, square-root bracketing, rational mesh construction, tail coverage, and window-specific search success |
| `pole-geometry.lisp` | Computed tie-avoiding height, unique nearest point and isolating circle for finite rational point data; no minimum-spacing assumption |
| `box-circles.lisp` | Verified square and distance enclosures, selected-box containment, and exclusion of all other boxes |
| `landau-bounds.lisp` | Computed geometric thresholds from Bernoulli's inequality; the normalized Landau coefficient contradiction |
| `log-bounds.lisp` | Rational rectangle sums for logarithms, computed subdivision count, and arbitrary positive width budgets |
| `euler-bounds.lisp` | Rational harmonic sums and Euler-constant enclosure propagation with a computed arbitrary positive width budget |
| `rpow-bounds.lisp` | Integer-power monotonicity, rational root bisection, power brackets and an arbitrary positive width budget for `x^(p/q)`, `x >= 1`, `0 <= p <= q`, `q > 0` |
| `prime-powers.lisp` | Trial-divisor primality, bounded prime-power search with soundness and completeness, and arbitrary-width von Mangoldt enclosures |
| `signal-bounds.lisp` | The actual smoothed sum and `Gz - C*x^(p/q)` evaluator; computed stopping bound and combined precision budget; arbitrary requested positive error width |
| `signal-search.lisp` | Evaluated window search, returned-address/certificate correctness, and success conditional only on finite peak transport |
| `window-index.lisp` | Bounded rational ceiling; computed index and checked kernel band with log/rounding error; all three geometric bounds under an explicit rational log-threshold check |
| `log-growth.lisp` | Doubling-block lower mass and an explicit integer window threshold; every larger rational window passes the index check and meets all three geometric targets |
| `log-partitions.lisp` | Comparison of arbitrary rational rectangle partitions; evaluator overlap, Cauchy error and Lipschitz bounds with explicit approximation losses |
| `rpow-continuity.lisp` | Polynomial order/reflection and cross-product root transport; overlap, Cauchy error and Lipschitz bounds for the actual rational-power evaluator |
| `euler-continuity.lisp` | Harmonic/log tail comparisons, overlap at different truncations/precisions, Cauchy bounds for the Euler evaluator and coarse rational bounds |
| `signal-continuity.lisp` | Full evaluated-signal transport, peak-to-search success, fixed search parameters, and a uniform rational ceiling with constant `C+1` from search failure |
| `signal-growth.lisp` | Lower smoothed-sum bounds independent of padding, coarse log bounds, and uniform two-sided quadratic growth of the lower `Gz` evaluator |
| `mellin-sums.lisp` | Rational complex disks, triangle inequality, one-sided weighted-sum cancellation, actual window/tail rows from failed search and proved growth, and explicit approximation-error propagation |
| `exp-bounds.lisp` | Exact rational Taylor terms/sums, computed starting index and precision depth, nested bands bounding later partial sums, arbitrary positive width, overlap/Cauchy bounds, and reciprocal negative-exponential enclosures |
| `exp-continuity.lisp` | Finite Taylor slope bounds and a uniform computed majorant; spatial transport without precision loss for exponential and reciprocal enclosures; explicit endpoint error budgets |
| `exp-addition.lisp` | Exact finite Taylor convolution; triangular/rectangular partial-sum comparison; product enclosure transport at independent precisions and quadratic rate shift |
| `negative-binomial.lisp` | Rising-binomial majorants for factorial-normalized Taylor terms; a rational geometric-tail potential, exact finite telescoping and negative-binomial moment bounds |
| `kernel-bounds.lisp` | Constructed nonnegative Mellin kernel weights, exact factorial factor and quadrature step, computed primitive precision, requested width, overlap and Cauchy bounds |
| `kernel-continuity.lisp` | Uniform Taylor-term slope bounds, computed kernel caps and slopes, precision-free enclosure transport and lower-endpoint spatial error budgets |
| `complex-bounds.lisp` | Rational complex arithmetic, disk propagation through products/powers, power-difference bounds, and finite quadratic remainders |
| `phase-bounds.lisp` | Rational Cayley phase samples, unit-disk validity, finite block/refinement error, arithmetic Cauchy bounds, and a computed precision-dependent step count |
| `phase-continuity.lisp` | Cayley and fixed-step Lipschitz bounds; spatial transport across different computed step counts, with the two refinement errors accounted for |
| `log-signal.lisp` | Computed rational sampling and transport for `Gz(exp u)`, including `u=0`; total requested width, overlap and Cauchy bounds |
| `log-signal-continuity.lisp` | A uniform interval cap, precision-free lower-to-upper spatial transport and an explicit positive mesh modulus for the log-variable signal |
| `mellin-integrand.lisp` | Independent coarse caps and component precision choices; rational complex samples, all constructor checks, product error and Cauchy bounds |
| `mellin-continuity.lisp` | Uniform signal/kernel caps and spatial transport of the actual sample constructor; separate argument/evaluation errors and a computed positive spatial modulus |
| `mellin-quadrature.lisp` | Fixed finite weighted-grid evaluation with a computed total precision budget, all constructor checks, rational output and Cauchy bounds across precision choices |
| `mellin-partitions.lisp` | Dyadic splitting preserves interval mass; quantitative comparison across refinement depths; computed grid depth and point precision; all constructor checks and Cauchy bounds for bounded-integral approximations |
| `mellin-meshes.lisp` | Comparison of arbitrary rational partitions while retaining each sample's anchor; exact dyadic endpoint/sum bridge; comparison of a whole dyadic sum with a differently partitioned prefix and tail |
| `mellin-tail-bounds.lisp` | Taylor scaling and two-term shifts give an inverse-square kernel bound; a telescoping potential bounds finite uniform kernel tails; computed cutoff and radius budgets |
| `mellin-integral.lisp` | Improper-transform evaluator with a computed cutoff and bounded quadrature; rational output, universal constructor checks and a total numerical error budget |
| `mellin-window.lisp` | Failed search bounds the actual computed Mellin coefficient pair through an explicit budget; height-zero grid comparison; exponential rate shift and uniformly small finite tails of actual weighted signal samples |
| `mellin-cutoffs.lisp` | Actual dyadic tails at the default cutoff; computed common mesh and point precision; arithmetic Cauchy bound for the default improper evaluator across changing cutoffs and grids, with an explicit precision budget |
| `kernel-mass.lisp` | Taylor-to-geometric kernel majorants; the actual Mellin sampler's uniform-grid weight sum is at most `2/rate^(j+1)` on sufficiently fine grids; computed cell count and spacing discharge that mesh requirement |
| `kernel-tilts.lisp` | Exact rational left/right tilts of finite negative-binomial moments; normalized tail bounds for the actual Mellin weights |
| `exp-geometric.lisp` | Finite Taylor comparisons with repeated products and reverse Euler bounds; rational geometric decay for the two tail factors |
| `kernel-window.lisp` | Checked-band concentration at rates 250, 300 and 200; normalization to rate 252; computed window threshold, derivative index and mesh absorb the growth factor 16 |
| `kernel-window-refinement.lisp` | Upper kernel enclosures inherit concentration; rational excess removes auxiliary sample precision; a computed primitive precision bounds the remaining error |
| `kernel-quadrature.lisp` | Upper-enclosure comparison between internal and external cell weights; finite tail sums inherit concentration with computed per-cell precision |
| `rpow-kernel.lisp` | Finite Taylor products and polynomial root brackets prove the kernel decay shift by every encoded rational exponent in `[0,1]`, at the actual log-signal sample point |
| `log-exp.lisp` | Finite inverse comparisons between log rectangles and Taylor sums; samples outside the actual spatial window lie in the two log-grid tails used by concentration |
| `mellin-kernel-budget.lisp` | Both branches of the actual window cap are bounded by shifted kernels; dyadic and default improper budgets inherit the bound; failed search gives the resulting coefficient disk estimate |
| `kernel-upper-mass.lisp` | Upper kernel enclosures have normalized total mass with an explicit primitive-precision cost |
| `mellin-normalization.lisp` | Sum the actual spatial mask using total mass and tail concentration; rational excess removes auxiliary precision and bounds the original finite window budget |
| `mellin-dyadic-normalization.lisp` | Exact dyadic-to-uniform budget decoding; computed common refinement and error bounds; failed search bounds the default coefficient pair at the computed window index |
| `complex-geometric.lisp` | Rational complex reciprocals, exact finite geometric identities, resolvent remainders, norm/disk bounds and finite geometric-average estimates |
| `cauchy-orbits.lisp` | Computed rational unit-circle rotations with separation through a given degree; exact zero moment and arbitrarily small signed nonzero moments at a computed sample count |
| `cauchy-polynomials.lisp` | Actual polynomial sample averages equal their signed-moment expansion; explicit coefficient-mass error bound and recovery of the selected list coefficient |
| `cauchy-extraction.lisp` | Computed count for any positive rational coefficient error; checked boundary values imply a finite Cauchy bound on the selected coefficient |
| `cauchy-resolvents.lisp` | Constructed geometric coefficient lists evaluate to the Taylor polynomial of an actual rational resolvent; a computed truncation order meets any positive rational error throughout the unit disk |
| `resolvent-sampling.lisp` | Actual resolvent sample averages recover its coefficients with computed truncation order, sampling count and total error |
| `pole-resolvents.lisp` | Actual rational principal parts reduce to the resolvent evaluator; computed sampling recovers the signed, radius-scaled pole coefficient, and checked clearance supplies convergence |
| `pole-lower.lisp` | Exact coefficient cancellation reconstructs the residue; total-coefficient and checked polynomial-remainder caps bound the actual residue |
| `zeta-pole-lower.lisp` | Derive a coefficient lower constraint from the explicit residue and multiplicity; finite Cauchy obstruction without an assumed coefficient lower bound |
| `zeta-pole-sums.lisp` | Finite families retain multiplicities; a checked clearance and computed residue mass bound all other pole coefficients |
| `pole-dominance.lisp` | Computed indices absorb the other poles and a checked unit-disc polynomial remainder, leaving an explicit lower constraint on the combined coefficient |
| `complex-exp.lisp` | Rational complex Taylor evaluator; real majorants, finite tails, Cauchy comparison, exact positive-real agreement, factorial moment identity and a computed uniform Taylor error |
| `kernel-moments.lisp` | Across moment indices, the actual kernel bands overlap after exact Taylor scaling; explicit error between the j-th lower endpoint and the scaled zeroth endpoint |
| `mellin-moments.lisp` | Actual signal, kernel and phase samples give a cross-index comparison; computed factor and precision bound the j-th sample against a scaled zeroth sample |
| `mellin-taylor-grid.lisp` | Computed node precisions lift that comparison to the actual finite quadrature output, with a requested total error |
| `exp-polynomials.lisp` | Constructed coefficient lists have proved coefficient access and evaluate exactly to finite mixtures of complex Taylor sums |
| `exp-mixture-bounds.lisp` | Computed common degree, node precision and total error budget give a polynomial approximation uniform on a checked disk |
| `mellin-polynomials.lisp` | Freeze actual zeroth-moment samples for one polynomial; recover the target quadrature coefficient, prove uniform mixture approximation, and derive an actual quadrature bound from the finite Cauchy checker |
| `complex-convolution.lisp` | Derive the complex Taylor convolution row and total-degree triangle identities from finite recurrences |
| `complex-exp-product.lisp` | A real Taylor tail bounds the complex product-rectangle error; computed magnitude caps for prefixes and evaluated values |
| `complex-exp-multiply.lisp` | A computed common Taylor order proves a quantitative multiplication law for the evaluated complex exponential |
| `complex-exp-negative.lisp` | Match negative real Taylor values to the existing reciprocal negative-exponential bands, with arbitrary-precision error and a computed precision constructor |
| `complex-exp-phase.lisp` | Compare a Cayley rotation to the imaginary Taylor evaluator, accumulate errors linearly using unit rotations, and bound the actual finite-step phase grid |
| `complex-phase-agreement.lisp` | Compute a step count and common positive precision identifying the actual phase sampler with the imaginary Taylor evaluator |
| `complex-damped-phase.lisp` | Compose negative-real and phase agreement with complex multiplication; a computed budget identifies their product with one complex exponential |
| `complex-disk-gap.lisp` | A computed positive rational slack separates a point outside a disk from a slightly enlarged disk, eliminating auxiliary comparison errors |
| `complex-kernel-agreement.lisp` | Independent reciprocal, phase and Taylor precisions give error at most their sum; the Taylor evaluator on the left half-plane has cap 1 plus its precision |
| `mellin-exponential-sample.lisp` | Identify the actual Mellin sample with one complex exponential, retaining its signal and exact moment mass; bound the error and compute a common precision |
| `mellin-shift-bounds.lisp` | Compute magnitude caps and a precision uniform across a checked shift disk; retain the actual sample's signal and moment mass |
| `mellin-sample-shift.lisp` | Compose exponential multiplication, signal transport and the two sample comparisons; prove the actual sample's complex-shift law at a computed common precision |
| `mellin-shift-mixture.lisp` | Freeze base samples over the shift disk, compare the finite mixture with actual shifted quadrature, and construct a polynomial with a proved uniform error |
| `mellin-shift-coefficients.lisp` | Recover the selected moment from the same frozen shift polynomial; transfer an accepted finite Cauchy boundary cap to the actual moment quadrature |
| `mellin-sample-scaling.lisp` | Prove width scaling for actual samples with independent precisions; a rational disk-gap argument removes auxiliary errors |
| `mellin-dyadic-cells.lisp` | Construct the actual dyadic partition as cells, compare cell and weighted sums, and transfer to the bounded integral constructor |
| `mellin-integral-polynomial.lisp` | Use the default improper evaluator's exact cutoff and depth; a checked polynomial boundary cap controls its computed moment output |
| `mellin-cutoff-order.lisp` | Prove cutoff ordering in the abscissa and compare a bounded evaluator above the default cutoff with the actual improper output |
| `mellin-uniform-mesh.lisp` | Compute one spatial slope and mesh that control every abscissa and height in a checked shift disk |
| `mellin-improper-polynomial.lisp` | One fixed polynomial uniformly approximates shifted improper evaluations and recovers the selected improper moment at the same precision; transfer a checked Cauchy cap |
| `pole-radius-dominance.lisp` | General physical contour radius; rescale regular coefficients by `R^(-j)` and compute a dominance index without requiring selected-pole distance below one |
| `polynomial-difference.lisp` | Exact finite polynomial subtraction; a checked boundary difference bounds each coefficient difference |
| `mellin-pole-bridge.lisp` | Construct a pole-model polynomial; compare it with the actual improper polynomial using finite boundary checks, then transfer radius-general pole dominance |
| `mellin-real-anchor.lisp` | Bound the retained height-zero moment using its own checked finite pole model |
| `mellin-window-certificate.lisp` | Compose both models with failed search; a strict scalar budget forces search success and a rational address with a positive lower certificate |
| `mellin-window-budget.lisp` | Compute geometric indices and comparison precision that discharge the scalar budget; conditional computed window witness |
| `complex-quotients.lisp` | Reciprocal and quotient error bounds with computed precision; derive a product's logarithmic derivative and its approximation error |
| `polynomial-factor-model.lisp` | Construct finite products and formal derivatives with multiplicities; derive their logarithmic principal-part sums and errors |
| `zeta-factor-transform.lisp` | Normalize finite factor contributions at 1, cancel the removable singularity, and derive the zeta-shaped residues plus an explicit regular correction |
| `polynomial-divided-difference.lisp` | Synthetic division constructs `(P(s)-P(a))/(s-a)` as a polynomial, including at `s=a`; prove its exact finite evaluation identity |
| `polynomial-maps.lisp` | Construct coefficient products and constant additions, with exact evaluation, length and coefficient access |
| `polynomial-normalization.lisp` | Normalize a polynomial logarithmic derivative at 1; construct its exact polynomial-plus-origin-pole split |
| `polynomial-affine.lisp` | Compute coefficients of `P(center+slope*w)` by linear multiplication and Horner composition |
| `pole-polynomials.lisp` | Construct a polynomial for `c/(a-R*w)`, compute its truncation, prove a degree-independent cap and guarantee its finite boundary checks |
| `polynomial-addition.lisp` | Add coefficient lists; bound unit-disk evaluations and finite boundary checks by the coefficient mass |
| `zeta-regular-model.lisp` | Build a regular certificate for finite factors plus a polynomial logarithmic derivative; prove normalized model identities, uniform approximation, boundary-check acceptance and compatibility with the Mellin regular validator |
| `complex-exp-increment.lisp` | Uniform compact caps and first-order error bounds for the actual complex exponential evaluator |
| `complex-exp-grid.lisp` | Sum finite rectangle defects by exact telescoping; derive endpoint-primitive error and precision stability |
| `complex-exp-integral.lisp` | Compute the grid count and point precision; prove the finite quadrature agrees with the endpoint expression at any requested error |
| `complex-laplace-basis.lisp` | Damped exponential decay and a computed cutoff; construct a finite exponential grid sum within `e` of `1/(sigma+i*height)` |
| `complex-exp-moment-grid.lisp` | Weighted rectangle defects and finite integration by parts; compare the `u*exp(z*u)` grid with its endpoint expression and prove precision stability |
| `complex-exp-moment-integral.lisp` | Compute sufficient mesh and point precision for the first-moment quadrature at any positive rational error |
| `complex-laplace-moment.lisp` | Quadratic damped decay and a computed cutoff; construct a finite first-moment sum within `e` of `1/(sigma+i*height)^2` |
| `complex-laplace-ramp.lisp` | Compute precision for the ramp's exponential decomposition; normalize a difference of computed Laplace quadratures to `1/(s*(s-1))` |
| `log-exp-inverse.lisp` | Finite Taylor sums have slope at least one; prove logarithm/exponential inverse error and replace the actual signal evaluator's `x*log(x)` correction by `x*u` within its requested error |
| `complex-laplace-shifted.lisp` | Compute quadrature and cutoff errors on a ray starting at any nonnegative rational point; normalize to the damped endpoint divided by the complex rate |
| `exp-log-ramp.lisp` | Bound `exp(lowerLog(n))` and the error from replacing the actual positive-part ramp by an extension starting at a computed logarithm, including samples near the breakpoint |
| `complex-log-ramp.lisp` | Compute common logarithm/exponential precision and two shifted quadratures; normalize their scaled difference to the computed Dirichlet endpoint times `1/(s*(s-1))` |
| `smoothed-ramp-sums.lisp` | Assemble breakpoint errors with the actual Mangoldt weights; compute a common truncation and total budget for the full log-variable signal decomposition |
| `signal-exponential-decomposition.lisp` | Freeze Mangoldt and Euler approximations and logarithmic breakpoints across the interval; compare the resulting finite exponential family with the actual signal at any independent precision |
| `signal-exponential-growth.lisp` | Bound the frozen family at every nonnegative rational node, including beyond its construction interval; derive a quadratic exponential majorant uniform in truncation |
| `mellin-frozen-tail.lisp` | Compare actual and frozen samples; compute a tail cutoff and finite grid with a bound uniform in truncation and independent positive sample precision, including tails starting after the cutoff |
| `mellin-frozen-quadrature.lisp` | Lift pointwise comparison through every dyadic refinement; compute model precision and bound the difference from the existing bounded Mellin constructor by half the requested error |
| `mellin-frozen-linearization.lisp` | Distribute dyadic quadrature exactly over the fixed finite prime family and correction terms; transfer the bounded evaluator's error and prove the ramp branches before and after each logarithmic breakpoint |
| `mellin-frozen-cutpoints.lisp` | Insert a logarithmic breakpoint into dyadic leaves; bound the crossing width by one mesh width, prove clipped ramp linearity and control the insertion error using the computed exponential jump |
| `mellin-frozen-cutpoint-sums.lisp` | Sum crossing errors with the actual Mangoldt weights and absorb them in the frozen model budget; all logarithmic breakpoints can be inserted while approximating the original bounded Mellin constructor within its requested error |
| `complex-exp-dyadic-grid.lisp` | Telescope exponential errors on clipped dyadic leaves; derive the endpoint primitive with explicit leaf-count and mesh error, and prove precision stability independent of depth |
| `complex-exp-dyadic-integral.lisp` | Compute a dyadic depth and point precision for any requested error; the clipped exponential sum approximates its endpoint formula, with endpoint precision independent of the leaf count |
| `complex-damped-product.lisp` | Prove exponential multiplication against the actual unit-disk damped sampler at independent precisions; eliminate the auxiliary comparison error, leaving no right-argument cap in the final bound |
| `complex-exp-dyadic-moment-grid.lisp` | Telescope clipped first-moment rectangles with their zeroth sum; derive the endpoint primitive with both propagated errors, bound changes of endpoint precision and handle empty leaves exactly |
| `mellin-clipped-exponential.lisp` | Compare all three frozen components of the zeroth Mellin transform with exponential or first-moment grids; independent precisions give an explicit height-independent bound proportional to interval width |
| `mellin-clipped-endpoints.lisp` | Compute clearances, target precision and depth for actual frozen constant/exponential components; prove their endpoint comparison while explicitly retaining the two fixed source-precision errors |
| `complex-exp-dyadic-moment-integral.lisp` | Compute the weighted mesh and point precision controlling both residuals; prove clipped first-moment endpoint approximation with a leaf-count-independent endpoint precision |
| `mellin-clipped-moment-endpoints.lisp` | Apply that constructor to the actual frozen first-moment component; allocate the extra error by its interval mass while retaining the two source-precision terms |
| `complex-exp-dyadic-refinement.lisp` | Preserve the unweighted endpoint on every finer dyadic mesh; recompute point precision using the actual leaf count while keeping endpoint precision fixed |
| `complex-exp-dyadic-moment-refinement.lisp` | Preserve the coupled first-moment endpoint on every finer mesh, with recomputed node precision and a fixed endpoint value |
| `mellin-clipped-refinement.lisp` | Transfer all three actual frozen component endpoint comparisons to a caller-selected finer mesh, retaining both source-precision terms |
| `mellin-clipped-common-mesh.lisp` | Compute one depth for all component types and every cutpoint, above any extra minimum; prove a common component estimate and rational endpoints |
| `mellin-clipped-family-endpoints.lisp` | Sum the computed ramp endpoints with the actual Mangoldt weights; certify the finite prime-family comparison with its explicit weighted error mass |
| `mellin-frozen-endpoints.lisp` | Assemble both corrections, restore crossing cells and actual signal samples, and compare the existing bounded zeroth Mellin constructor with the full endpoint expression |
| `mellin-endpoint-budgets.lisp` | Bound the weighted endpoint mass independently of precision; compute one height-independent internal request controlling the complete bounded Mellin endpoint error |
| `mellin-improper-endpoints.lisp` | Prove endpoint values are rational, compare the computed family with the actual improper evaluator in `sigma>2`, and derive its Cauchy bound across changing cutoffs and coefficients |
| `complex-log-ramp-independent.lisp` | Normalize the shifted exponential and ramp endpoints at a fixed computed logarithm while independently refining the complex exponential precision; retain both error terms |
| `complex-log-ramp-family.lisp` | Normalize the complete finite Mangoldt-weighted ray-endpoint family and factor its Dirichlet sum; compute node precision with a total bound retaining the frozen logarithm budget |
| `complex-exp-boundaries.lisp` | Decompose zeroth and first-moment primitives into exact lower and upper boundaries, including empty clipped intervals; normalize damped boundaries and their values at zero |
| `mellin-dirichlet-boundaries.lisp` | Assemble the full finite primitive family and both corrections with an explicit upper boundary; at common node precision, normalize their sum to the finite Dirichlet model with the frozen logarithm error retained |
| `mellin-endpoint-precision.lisp` | Transfer all component and weighted-family endpoint precisions to a computed common node precision; bound the full transfer by a precision-independent interval factor |
| `mellin-dirichlet-comparison.lisp` | Preserve Dirichlet normalization under finer node precision and compose the actual bounded and improper Mellin comparisons, retaining the explicit computed boundary correction |
| `signal-exponential-refinement.lisp` | Refine point-exponential precision independently of fixed coefficients and logarithmic cutpoints; preserve rationality and the global quadratic growth bound beyond the construction cap |
| `mellin-refined-tail.lisp` | Transfer the refined growth bound to Mellin samples and finite tail grids, with computed cutoffs and bounds uniform in truncation and both point precisions |
| `mellin-refined-dyadic-tail.lisp` | Prove native-sampler agreement and dyadic tail bounds; the original mass-four improper cutoff gives radius `5/4*cutoffError` for the refined mass-five family |
| `mellin-refined-linearization.lisp` | Distribute refined dyadic quadrature exactly over the fixed prime family and both correction terms while keeping point-exponential precision independent |
| `mellin-refined-cutpoints.lisp` | Bound weighted crossing jumps at independent exponential precision; insert all frozen logarithmic cutpoints on an interval independent of the construction cap |
| `mellin-refined-endpoints.lisp` | Compare the complete refined dyadic family with its computed endpoints, with both caps independent; compose its tail estimate with the explicit endpoint comparison error |
| `mellin-refined-endpoint-budgets.lisp` | Compute a common request and mesh making the tail endpoint comparison error at most `e/16`; at the original improper cutoff, the complete endpoint family has radius `5/4*cutoffError+e/16` |
| `mellin-interval-precision.lisp` | Transfer exponential and first-moment endpoints on any nonnegative interval to one computed finer node precision, retaining the starting point in the moment budget |
| `mellin-interval-boundaries.lisp` | Prove the full fixed-coefficient interval primitive equals the difference of its upper boundaries; transfer all weighted endpoints to it with radius `G*r/16` |
| `mellin-boundary-tail.lisp` | Compose refined tail and precision budgets into common-node boundary difference bounds, valid at every finer positive precision; obtain radius `5/4*cutoffError+e/8` at the original improper cutoff |
| `mellin-boundary-precision.lisp` | Derive boundary Cauchy estimates from precision-independent values at zero; prove the actual computed Dirichlet boundary changes by at most `e/256` under finer node precision |
| `complex-boundary-decay.lisp` | Bound both damped exponential boundary components by `8/T+2*(T+1)*delta`, independently of height, for `T>=1` and real rate above one |
| `mellin-far-boundary.lisp` | Lift decay through the fixed Mangoldt-weighted family and both corrections; compute a far endpoint and node threshold attaining any requested boundary error |
| `mellin-dirichlet-decay.lisp` | Compose common-node tails, near-boundary stability and far decay; bound the original computed boundary by `2e` and compare the actual improper Mellin evaluator directly with the finite Dirichlet model within `3e` |
| `complex-damped-continuity.lisp` | Prove uniform spatial Cauchy bounds in the closed negative half-plane; Laplace transport costs `2*(rate+abs(height))*abs(u-v)+32*(e1+e2)`, independently of the base arguments |
| `dirichlet-term-transport.lisp` | Bound Mangoldt precision changes and logarithmic cutpoint transport; absorb weighted logarithm errors into the existing model budget, allowing independent truncation totals |
| `dirichlet-family-precision.lisp` | Sum precision errors uniformly in the model budget for common prefixes with independent totals; compute a finite Dirichlet value with fixed-count Cauchy radius `e1+e2` and compare any prefix using a larger truncation budget |
| `dirichlet-cubic-decay.lisp` | Chain three logarithmic rate shifts for `sigma>3`; bound actual weighted Dirichlet terms by `2/n^2` plus explicit node and logarithm errors |
| `dirichlet-tails.lisp` | Sum the computed node cost, telescope the reciprocal majorant, and bound finite tails by `2/M+cost(N)*delta+3*m/8` for `1<=M<=N<=total` |
| `dirichlet-finite-cauchy.lisp` | Compute auxiliary node precision controlling both the tail cost and finite refinement; prove varying-count Cauchy radius `2/M+4*(e1+e2)` |
| `dirichlet-series.lisp` | Compute the series cutoff from its error, prove rationality and Cauchy radius `e1+e2` at `sigma>3`, and compare with every longer finite approximation |
| `mellin-series-precision.lisp` | Bound count-dependent node and coefficient errors by a gain independent of the cutoff; compare the existing Mellin prime sum with the canonical finite Dirichlet value |
| `dirichlet-transform.lisp` | Normalize the series by the Mellin rational factors and Euler correction; prove transport, rationality and Cauchy bounds for the computed transform |
| `mellin-dirichlet-series.lisp` | Compute an auxiliary request whose Mellin cutoff covers the series terms; prove `disk(I(e1)-A(e2),5*e1+e2)` for the actual improper evaluator and normalized series at `sigma>3` |
| `log-multiplication.lisp` | Preserve logarithm rectangle sums under exact partition scaling; concatenate partitions to prove product enclosure overlap and lower-logarithm multiplicativity with three independent requests |
| `dirichlet-product.lisp` | Prove multiplication of the actual computed `n^(-s)` samples with independent logarithm and exponential errors; compute a common precision attaining any requested product error |
| `zeta-term-transport.lisp` | Define explicit ordinary/logarithm coefficient modes, prove their bounds and precision stability, and transfer the weighted logarithm transport budget to both |
| `zeta-family-precision.lisp` | Construct actual finite sums with the exact `n=1` term; prove rationality, common-prefix precision bounds and fixed-count Cauchy control |
| `zeta-tails.lisp` | Lift cubic decay to both coefficient modes and telescope their finite tails with the shared computed cost and tail radius |
| `zeta-finite-cauchy.lisp` | Use a common finer family to compare the explicit zeta sums at different counts, with radius `2/M+4*(e1+e2)` |
| `zeta-series.lisp` | Compute ordinary and logarithm-weighted series values at `sigma>3`; prove rationality, Cauchy radius `e1+e2` and comparison with every longer finite approximation |
| `zeta-series-clearance.lisp` | Recover unweighted cubic decay; bound the ordinary series around 1, prove squared-norm clearance `1/16` and reciprocal cap 4, and bound the logarithm-weighted series by 3 |
| `zeta-log-quotient.lisp` | Compute a precision with nonzero denominator, prove the explicit log/ordinary series ratio is rational and Cauchy, and recover the numerator by exact multiplication |
| `integer-divisibility.lisp` | Bridge integer-quotient divisibility to MOD tests; prove transitivity, integer linear combinations, positive divisor bounds and prime-divisor dichotomy |
| `bezout-gcd.lisp` | Compute a terminating gcd with integer Bézout coefficients and common-divisor proofs; derive Euclid's lemma and coprime product cancellation |
| `prime-power-divisibility.lisp` | Prove prime divisors of powers, unique bases and exponents, the exact prime-power search result, addition of exponents and divisibility ordering |
| `least-prime-divisor.lisp` | Compute the least divisor by bounded search; prove it prime and prove its integer quotient is positive and strictly smaller |
| `prime-factorization.lisp` | Compute repeated least-prime division; prove prime factors, the exact input product and prime-divisor membership |
| `prime-valuations.lisp` | Count occurrences of primes; prove common-factor cancellation, removal of distinct prime factors and the exact prime-power divisibility criterion |
| `prime-power-divisors.lisp` | Enumerate one prime power per factor occurrence; prove completeness for actual prime-power divisors and absence of duplicates |
| `mangoldt-divisor-sum.lisp` | Reindex the actual finite divisor sum of lower Mangoldt values exactly as the factor-log sum, using the computed duplicate-free enumeration |
| `mangoldt-divisor-log.lisp` | Bound the finite divisor sum's logarithm error by `3*L*e+logError` for `L` computed factors and provide a precision meeting any positive target error |
| `finite-dirichlet-convolution.lisp` | Prove positive divisor quotient bounds and exact hyperbola reindexing for arbitrary rational coefficient and complex-node tables, preserving both factor cutoffs |
| `mangoldt-dirichlet-convolution.lisp` | Construct actual Mangoldt and complex-power tables; reindex their hyperbola and replace divisor coefficients by lower logarithms with a computed error budget |
| `dirichlet-hyperbola-product.lisp` | Bound actual `E(a)*E(b)` product errors over the finite hyperbola and compute one shared precision for any requested finite convolution error |
| `hyperbola-majorants.lisp` | Prove finite reciprocal-square sums and tails, square containment, and the absolute hyperbolic majorant `16/M` uniformly in both rectangle sizes |
| `dirichlet-hyperbola-tail.lisp` | Split full products into hyperbola and tail; bound actual omitted samples including rounding costs and compute a cutoff and precision for the product of complete finite prefixes |
| `dirichlet-common-precision.lisp` | Unify Mangoldt, logarithm and ordinary coefficients; compare shared-precision prefixes with the native finite and Cauchy-series evaluators using computed refinement thresholds |
| `dirichlet-series-product.lisp` | Construct common cutoffs and requests; prove the actual native series product identity with fixed computed caps and independent precision errors, removing the last slack by rational disk-gap refinement |
| `dirichlet-series-ratio.lisp` | Use zeta denominator clearance to identify the Mangoldt series and the existing zeta-series ratio; prove independent-error bounds and compute a common request meeting any positive budget |
| `mellin-zeta-series.lisp` | Normalize the zeta-series ratio with the actual transform factors and Euler term; prove Cauchy control and comparison with the actual improper Mellin evaluator within `5*e1+e2` |
| `log-cell-bounds.lisp` | Compare actual native logarithm grids with one-cell rectangles; prove the adjacent-integer normalization and its explicit error |
| `exp-quadratic-decay.lisp` | Prove quadratic positive exponential growth and reciprocal-square decay of the actual negative-exponential lower evaluator |
| `complex-damping-cap.lisp` | Retain the actual damping factor in complex exponential bounds and derive a quadratic decay cap with explicit point errors |
| `dirichlet-dyadic-decay.lisp` | Prove native complex-power decay in every positive real half-plane, with cap 32/(sigma^2*j^2)+3e beyond 2^j |
| `complex-euler-cell.lisp` | Prove adjacent Euler cancellation from native logarithm cells and the actual complex exponential first-order error |
| `euler-dirichlet-cells.lisp` | Compare actual adjacent Dirichlet corrections with the damped Euler factor; prove cell decay and compute every rounding coefficient |
| `euler-dirichlet-prefix.lisp` | Prove exact finite Euler telescoping for the actual common-precision ordinary zeta prefix, retaining its explicit boundary term |
| `euler-dirichlet-blocks.lisp` | Sum actual corrections over dyadic blocks; bound reciprocal cell mass by one and prove a reciprocal-square block cap with computed rounding costs |
| `euler-dirichlet-telescoping.lisp` | Identify actual Euler segments and dyadic blocks with exact differences of the original common-precision zeta prefixes |
| `euler-dirichlet-tail.lisp` | Sum arbitrary finite dyadic tails, retain their computed rounding costs and prove the actual prefix bound D/(J-1)+T*q for every positive real part |
| `euler-dirichlet-tail-budget.lisp` | Compute a sufficient starting block and point precision for any positive tail budget; prove the bound for every finer positive request |
| `euler-dirichlet-precision.lisp` | Prove independent point-precision transport for ordinary and Euler prefixes throughout sigma>=0, including the dyadic endpoint costs |
| `euler-continuation.lisp` | Construct a finite rational Euler value for sigma>0; compute comparison cutoffs and requests and prove Cauchy radius e1+e2 without an analytic continuation premise |
| `euler-zeta-prefix.lisp` | Compare actual finite Euler prefixes with the pole-removed native zeta series, retaining the boundary and independent numerical errors |
| `euler-zeta-budget.lisp` | Compute one dyadic endpoint and shared point request that meet the native series cutoff, Euler tail and boundary-error budgets |
| `euler-zeta-agreement.lisp` | Identify the Euler and pole-removed native zeta Cauchy names by rational disk-gap refinement; compute a common request meeting any positive error target |
| `zeta-euler-value.lisp` | Normalize by the exact reciprocal of s-1; construct a zeta Cauchy value for sigma>0 away from the pole and prove independent-error and computed agreement with the native series for sigma>3 |
| `euler-fixed-truncation.lisp` | Compare the actual Euler value at any independent accuracy with one fixed dyadic prefix; compute truncation and precision for a requested error |
| `euler-disk-bounds.lisp` | Bound the Euler tail and point-precision costs uniformly on every rational closed disk strictly inside the positive half-plane; compute one cutoff and request for all its points |
| `exp-mixture-precision.lisp` | Compare existing exponential mixtures with common-precision samples; construct affine rational polynomials and retain explicit mass-dependent errors |
| `euler-exponential-mixtures.lisp` | Construct the actual frozen-logarithm ordinary and boundary mixtures and identify their combination with the finite Euler prefix exactly |
| `euler-prefix-polynomial.lisp` | Construct rational polynomial coefficients for the actual finite Euler prefix, prove the exact evaluation formula and propagate both mixture errors |
| `euler-uniform-polynomial.lisp` | Compute one polynomial uniformly approximating the actual Euler Cauchy value on a closed disk; prove independent-request comparison and pairwise Cauchy bounds |
| `polynomial-coefficient-maps.lisp` | Prove exact coefficient and evaluation rules for physical-disk rescaling and zero padding; construct comparable polynomial differences with independent input lengths |
| `euler-coefficient-cauchy.lisp` | Extract normalized Euler coefficients from the actual uniform polynomials; construct all finite Cauchy boundary checks and prove independent-degree and independent-error Cauchy bounds |
| `euler-coefficient-bounds.lisp` | Compute one coarse-polynomial cap independent of degree, index and precision; bound all normalized Euler coefficients without an assumed analytic estimate |
| `euler-local-coefficients.lisp` | Construct physical Euler coefficients with radius-adjusted precision; identify them with actual polynomial coefficients and prove Cauchy radius e1+e2 and cap C/r^k |
| `polynomial-quadratic-bounds.lisp` | Compute a failed-coefficient witness; prove capped finite tails, the exact quadratic remainder identity and perturbation bounds for linear remainders |
| `euler-quadratic-increment.lisp` | Prove the actual Euler polynomials satisfy the cap checker; transfer their quadratic remainder to the evaluator with independent value and slope errors, then convert to physical coordinates |
| `euler-derivative-modulus.lisp` | Compute a positive step modulus and compatible value/slope precisions; prove linear increment error at most error times step radius, including independent finer requests |
| `euler-difference-quotient.lisp` | Compute reciprocal clearance from a nonzero rational complex step; prove an explicit difference-quotient error bound for the actual Euler evaluator and first physical coefficient |
| `polynomial-prefix-bounds.lisp` | Prove exact truncation and padded-prefix coefficient identities; preserve tail coefficient caps and bound the finite remainder beyond any requested degree |
| `euler-series-coefficients.lisp` | Construct finite lists of canonical Euler coefficients and prove coefficientwise and polynomial comparison with independently requested Euler approximants |
| `euler-local-series.lisp` | Compute the local series cutoff and shared coefficient request; prove uniform agreement with the actual Euler evaluator on half disks and Cauchy radius (e1+e2)/2 |
| `polynomial-geometric-bounds.lisp` | Compute the gain 1/(1-h) and prove geometric finite tails and prefix remainders on every rational disk 0<=h<1 |
| `euler-inner-series.lisp` | Compute cutoff and coefficient precision for any strict inner disk; prove uniform Euler agreement, Cauchy bounds and a value cap independent of precision |
| `polynomial-derivatives.lisp` | Compute the finite Horner derivative; prove exact constant/linear coefficient rules for affine substitution, constant addition and multiplication by a linear factor |
| `exp-mixture-derivatives.lisp` | Construct rate-weighted nodes and prove exact coefficient recurrences, finite polynomial derivatives and affine first-coefficient identities |
| `exp-mixture-derivative-bounds.lisp` | Compute a degree sufficient for weighted-mixture derivatives and prove uniform comparison with actual common-precision exponential samples |
| `euler-weighted-mixtures.lisp` | Identify the weighted Euler nodes with native log-weighted prefixes and boundary samples; prove precision-independent quadratic mass bounds |
| `polynomial-sum-coefficients.lisp` | Prove exact coefficient extraction for polynomial sums and the constant coefficient after adding a constant |
| `euler-prefix-derivatives.lisp` | Compute a common derivative degree and compare the finite Euler polynomial's first coefficient with its actual ordinary, log-weighted and boundary prefixes |
| `euler-derivative-series.lisp` | Prove explicit derivative boundary decay, a native derivative candidate with Cauchy bounds, and finite Euler polynomial comparison with that candidate |
| `euler-refined-polynomial.lisp` | Refine the dyadic truncation and shared point precision independently; preserve uniform Euler approximation and compare with canonical uniform polynomials |
| `euler-refined-coefficients.lisp` | Construct all finite Cauchy checks for refined polynomial differences; compare their normalized coefficients and first physical coefficient with the canonical Euler slope |
| `euler-derivative-alignment.lisp` | Compute compatible truncation, shared precision and derivative degree in that order; prove their combined coefficient and native-series error budget |
| `euler-native-derivative.lisp` | Identify the canonical Euler slope with the native ordinary-minus-logweighted derivative series at independent requests; compute a common refinement for any positive error |
| `complex-quotient-increments.lisp` | Prove shifted denominator clearance, the exact finite quotient increment identity and its quantitative derivative-error bound |
| `zeta-euler-derivative.lisp` | Construct a normalized derivative request and rational Cauchy name; prove precision-independent numerator caps for its difference quotient |
| `zeta-difference-quotient.lisp` | Compute the step modulus and actual zeta endpoint precisions; prove the reciprocal-normalized evaluator's finite difference quotient approximates its derivative name |
| `zeta-native-derivative.lisp` | Identify the normalized derivative with the negative log-weighted native series at independent requests and compute a common refinement |
| `zeta-euler-clearance.lisp` | Transfer the native ordinary-series cap to the actual zeta evaluator; prove squared-norm clearance 1/16 and reciprocal cap 4 at requests at most 1 |
| `zeta-euler-log-derivative.lisp` | Construct the evaluated negative logarithmic derivative with a checked denominator and a computed request; prove a fixed numerator cap and Cauchy radius e1+e2 |
| `zeta-native-log-derivative.lisp` | Identify the evaluated negative logarithmic derivative with the native zeta series ratio at independent requests and prove a common refinement |
| `mellin-zeta-derivative.lisp` | Normalize the evaluated negative logarithmic derivative and Euler correction; identify its Cauchy value with the actual improper Mellin evaluator within 5*eI+eF/2 |
| `euler-anchor-exponential.lisp` | Extend exponential/logarithm normalization to rate one with independent log and node errors |
| `euler-anchor-value.lisp` | Prove the computed endpoint estimate and actual Euler Cauchy-name identity V(1)=1, with error e/4 |
| `euler-anchor-prefix.lisp` | Compare rate-one nodes and ordinary prefixes with reciprocals and harmonic sums; bound the finite derivative against the Euler-constant enclosure |
| `euler-anchor-budget.lisp` | Compute cutoff, shared precision and derivative degree; prove the total anchor comparison budget |
| `euler-anchor-derivative.lisp` | Identify the actual first physical coefficient at one with the Euler constant at independent requests and prove a computed common refinement |
| `euler-value-clearance.lisp` | Check one actual coarse Euler value; prove nonzero finer values, squared-norm and reciprocal bounds, and generate accepted anchor checks |
| `euler-log-derivative.lisp` | Construct the actual checked quotient V'/V with computed precision, fixed cap and Cauchy bounds; prove agreement independent of the accepted coarse check |
| `euler-log-derivative-anchor.lisp` | Generate a fixed accepted clearance check at one and identify the checked quotient with the Euler constant at independent requests |
| `euler-zeta-clearance.lisp` | Generate accepted coarse Euler nonzero checks throughout sigma>3 from the actual normalized zeta clearance |
| `euler-zeta-log-algebra.lisp` | Prove exact finite value and derivative factors, control nested requests, and identify their logarithmic-derivative quotient |
| `euler-zeta-log-derivative.lisp` | Compute comparison budgets and identify the actual Euler quotient with 1/(s-1) minus the negative zeta logarithmic derivative at independent requests |
| `euler-log-transform.lisp` | Prove the exact Euler logarithmic-derivative normalization and explicit transport amplification on the positive half-plane away from one |
| `mellin-euler-log-derivative.lisp` | Construct the normalized Euler Cauchy family independently of accepted coarse checks and identify it with the actual improper Mellin evaluator using generated right-plane checks |
| `polynomial-derivative-coefficients.lisp` | Construct the weighted coefficient list of a formal derivative and prove exact polynomial evaluation |
| `euler-shifted-polynomial.lisp` | Shift one global Euler polynomial to every admissible center; prove uniform comparison with local polynomials and identity at zero |
| `euler-shifted-coefficients.lisp` | Generate all finite boundary checks and extract every shifted coefficient with physical error E/delta^k+e |
| `euler-coefficient-radii.lisp` | Prove local coefficient agreement across arbitrary admissible extraction radii using one global polynomial |
| `euler-uniform-derivative.lisp` | Construct one derivative polynomial for an inner disk and prove uniform comparison with local slopes at arbitrary admissible coefficient radii |
| `euler-uniform-derivative-bounds.lisp` | Compute finite polynomial disk caps and fixed bounds for local slopes and all fine derivative models, independent of target and precision |
| `polynomial-product.lisp` | Construct actual product coefficient lists by Horner convolution and prove validity and exact evaluation |
| `polynomial-geometric-sum.lisp` | Construct finite geometric-sum polynomials; prove exact evaluation, geometric inverse error and a fixed cap under a half-disk residual bound |
| `polynomial-disk-increments.lisp` | Compute a polynomial variation cap from its divided difference and bound every increment throughout a disk |
| `polynomial-half-disk-slope.lisp` | Compute a local increment bound from the maximum normalized coefficient size |
| `euler-nonzero-neighborhood.lisp` | Generate a positive nonzero disk from one actual coarse Euler check; prove uniform value and polynomial clearance and accepted shifted checks |
| `polynomial-inverse.lisp` | Construct residual and inverse polynomials with exact evaluation, computed geometric truncation, error bounds and a fixed half-disk cap |
| `euler-uniform-inverse.lisp` | Generate the residual half-disk and explicit reciprocal polynomials for the actual Euler family on the computed neighborhood, with uniform errors and caps |
| `euler-uniform-log-derivative.lisp` | Multiply actual derivative and inverse polynomials; prove uniform agreement with the checked Euler quotient at every admissible local radius, with fixed model and fine-value caps |
| `euler-log-polynomial-cauchy.lisp` | Prove uniform quotient-polynomial agreement across independent degree and accuracy choices |
| `polynomial-cauchy-caps.lisp` | Compute a finite boundary test from the first failed coefficient and prove it certifies every coefficient cap |
| `euler-log-coefficient-caps.lisp` | Generate all boundary checks for quotient polynomials and their normalized differences; certify degree-independent coefficient caps |
| `polynomial-tail-stability.lisp` | Prove half-disk tail bounds, padding stability, tail-difference bounds and the exact first-tail identity at the origin |
| `euler-log-divided-difference.lisp` | Construct physical divided-difference polynomials, prove their exact identity and uniform cap, and control their Cauchy error including the center |
| `euler-log-polynomial-anchor.lisp` | Compare quotient polynomials to every accepted coarse check and identify their constant coefficient with the actual Euler-constant name |
| `euler-removable-numerator.lisp` | Compute the fixed neighborhood, requests and normalized numerator polynomials; prove exact evaluation, a fixed cap and uniform Cauchy bounds |
| `euler-removable-value.lisp` | Construct a bounded local rational Cauchy family on a disk containing one, with comparison across independent target degrees and precisions |
| `complex-normalized-extension.lisp` | Prove exact normalization cancellation with complex anchor data, quantitative transport and agreement with the real-gamma Euler transform |
| `euler-removable-agreement.lisp` | Identify the local Cauchy family with the actual normalized Euler evaluator away from one at independent requests and accepted checks |
| `euler-removable-extension.lisp` | Supply the global normalized evaluator's computed value at one; prove rationality, Cauchy and check independence, local model comparison at the center, and preserved right-plane Mellin agreement |
| `linear-inverse-polynomials.lisp` | Construct polynomial inverses of affine denominators on computed quarter-L1 disks; prove nonzero clearance, arbitrary error and degree-independent caps |
| `polynomial-subtraction.lisp` | Construct subtraction for coefficient lists of unrelated lengths and prove validity, length and exact evaluation |
| `normalized-local-polynomial.lisp` | Construct the normalized local polynomial from quotient and affine-inverse polynomials; prove exact normalization, fixed caps, approximation and value/gamma transport bounds |
| `euler-removable-polynomial.lisp` | Replace the removable model's rational denominator by an explicit inverse polynomial; prove uniform comparison through one and fixed polynomial and evaluator caps |
| `euler-normalized-disk.lisp` | Compute disks avoiding zero and one, normalization budgets and gamma requests from an accepted coarse Euler check |
| `euler-normalized-polynomial.lisp` | Construct a point-independent normalized polynomial away from one; prove its fixed cap and agreement with the actual extended evaluator at independent requests |
| `euler-local-normalized-model.lisp` | Unify normalized polynomial models at and away from one; generate shifted checks and prove uniform comparison, polynomial Cauchy bounds and a fixed evaluator cap |
| `euler-local-normalized-coefficients.lisp` | Generate finite boundary checks and degree-independent coefficient caps for normalized models and padded differences, including the removable center |
| `polynomial-capped-coefficients.lisp` | Read capped coefficients, including indices outside the list; bound arbitrary rescaled coefficient differences from padded polynomial caps |
| `euler-normalized-coefficient-values.lisp` | Construct canonical normalized coefficient evaluators with degree-independent caps and half-sum Cauchy and polynomial comparison errors |
| `euler-normalized-series-coefficients.lisp` | Assemble finite lists of canonical normalized coefficients; prove prefix coefficient caps, exact access and uniform polynomial comparison |
| `euler-normalized-inner-series.lisp` | Compute a cutoff and coefficient request on any strict inner disk; reconstruct the actual normalized evaluator through one, with fixed caps and Cauchy bounds across inner radii |
| `euler-normalized-physical-coefficients.lisp` | Rescale canonical normalized coefficients to physical coordinates; prove exact polynomial coefficient identities, radius-adjusted requests, fixed caps and Cauchy bounds |
| `euler-normalized-mellin-series.lisp` | Identify the constructed normalized local series with the actual improper Mellin evaluator for real part above three; compute requests meeting any output error |
| `euler-normalized-overlap.lisp` | Prove agreement of independently constructed polynomial and series models at common physical points, allowing different centers, radii and coarse checks |
| `complex-segments.lisp` | Prove affine segment identities and convex disk bounds for every rational interpolation parameter |
| `euler-contour-patches.lisp` | Package coarse Euler checks as finite patches; prove endpoint membership covers the whole segment and generates accepted checks at every point |
| `euler-contour-segment-models.lisp` | Construct actual affine polynomial coefficient lists along covered segments; prove exact evaluation, fixed caps, Cauchy bounds and native evaluator agreement |
| `euler-contour-cover.lisp` | Check finite edge records and their patch assignments; compute a shared cap and prove coverage and accepted checks for every indexed segment point |
| `euler-contour-models.lisp` | Construct all contour polynomial models and a computed evaluator; prove exact list access, uniform cap, independent-request comparison and Cauchy bounds |
| `euler-contour-closed.lisp` | Check closed chains and cyclic successor indices; prove endpoint equality and polynomial and native evaluator agreement at every join, including closure |
| `euler-normalized-physical-comparison.lisp` | Compare canonical physical coefficients with any constructed normalized local polynomial, with explicit radius scaling |
| `euler-mellin-local-polynomial.lisp` | Construct reflected local Euler polynomials inside the native Mellin region; generate shifted checks, fixed caps and exact signed coefficient identities |
| `euler-mellin-polynomial-comparison.lisp` | Compare the actual reflected Euler and improper Mellin polynomials uniformly on a computed disk, with independent degrees and requests |
| `euler-mellin-coefficient-comparison.lisp` | Generate every finite boundary check for the polynomial difference and bound every physical coefficient, including indices beyond either polynomial's length |
| `euler-mellin-moments.lisp` | Identify every actual Mellin moment with the signed normalized Euler coefficient; remove auxiliary errors and compute requests for any output error |
| `euler-mellin-native-coefficients.lisp` | Construct canonical right-plane coefficient names from generated checks; prove caps, Cauchy bounds, all-index moment comparison and agreement with independently chosen local models |
| `euler-window-coefficients.lisp` | Transfer failed window search to the actual canonical Euler coefficient family; retain the real coefficient and eliminate every auxiliary Mellin error |
| `unit-circle-charts.lisp` | Compute a sign and bounded rational inverse parameter for every rational unit-circle point, including the point omitted by a single chart |
| `complex-circles.lisp` | Construct physical circle points; prove exact distance, Lipschitz arc bounds and reconstruction from the computed inverse chart |
| `euler-circle-arcs.lisp` | Use one midpoint clearance to cover an entire circular arc and generate accepted shifted Euler checks at every rational parameter |
| `euler-circle-cover.lisp` | Check two finite interval chains and compute a covering patch for every rational unit point; derive shared caps and coverage of every finite Cauchy rotation sample |
| `euler-circle-models.lisp` | Construct spatial polynomial and native value models on a covered circle; prove fixed caps, independent-request comparisons, Cauchy bounds and agreement between different covers |
| `euler-circle-grid.lisp` | Construct both chart covers and all midpoint patches on a uniform rational grid; finite coarse value and radius checks generate coverage and a fixed cap for every Cauchy sample |
| `euler-circle-clearance.lisp` | Compute a positive minimum shifted anchor for a finite circle cover; prove uniform native denominator clearance and a canonical larger approximation disk |
| `euler-circle-global-polynomial.lisp` | Construct one global Euler polynomial and its own formal derivative; prove uniform value and derivative comparisons, fixed derivative caps and denominator clearance on the covered circle |
| `euler-circle-global-quotient.lisp` | Prove actual global polynomial quotient agreement with the native Euler logarithmic derivative; compute output requests, fixed caps and Cauchy bounds, and connect the same polynomial model to every generated-grid Cauchy sample |
| `complex-orientation.lisp` | Prove rational determinant and dot identities and show that a disk separated from zero lies in an open positive half-plane |
| `ray-crossing.lisp` | Compute integer ray crossings with a fixed convention at boundary vertices; prove reversal, half-plane triangle cancellation and an edge potential |
| `polygon-index.lisp` | Construct path and closed-polygon indices; prove concatenation, integer bounds, half-plane cancellation and quadrilateral decomposition |
| `grid-index.lisp` | Prove exact cancellation of all internal edges in rectangular complex-value grids, leaving the oriented outer boundary |
| `grid-root-search.lisp` | Prove bounded grid search returns a small complex value when the boundary index is nonzero and the finite cell-variation checks pass |
| `polynomial-lipschitz.lisp` | Compute a two-point Lipschitz cap directly from finite polynomial coefficients and prove its variation bound on a disk |
| `polynomial-grid.lisp` | Construct exact polynomial values on a rational square grid; prove shape, indexed access, point bounds and coefficient-controlled cell variation |
| `polynomial-root-search.lisp` | Compute mesh size from the coefficients and requested error; a nonzero computed boundary index guarantees a returned rational point in the square with polynomial magnitude at most that error |
| `polygon-refinement.lisp` | Replace checked polygon edges by arbitrary finite half-plane chains; derive checks from rational distances and preserve path endpoints and the closed index |
| `polygon-homotopy.lisp` | Close finite polygons with exact index identities; checked nonzero collars prove index invariance under polygon deformation |
| `polynomial-edge-refinement.lisp` | Generate rational segment meshes; computed coefficient caps and endpoint clearance preserve an actual polynomial edge's crossing contribution at every finite subdivision |
| `polynomial-path-refinement.lisp` | Assemble actual polynomial edge samples along a finite path; generated half-plane checks preserve its polygon index for every positive subdivision count |
| `polygon-paths.lisp` | Prove finite path concatenation and reversal, swapped endpoints, integer indices and reverse-orientation identities |
| `grid-perimeter.lisp` | Construct the explicit four-side perimeter with duplicate corners; prove its shape, vertex count and equality with the actual grid boundary index |
| `polynomial-grid-perimeter.lisp` | Construct domain square boundaries from the identity polynomial grid; actual polynomial evaluation maps them exactly onto the search-grid perimeter |
| `polynomial-line-sampling.lisp` | Construct uniform polynomial segment samples and integer crossing sums; prove exact splitting, endpoint and row-index formulas |
| `polynomial-line-refinement.lisp` | Prove rational affine reparameterization and exact crossing-index preservation at every integer multiple of a fixed checked uniform path |
| `polynomial-grid-columns.lisp` | Identify actual top rows and side columns, with exact endpoint formulas for the rectangular polynomial grid |
| `polynomial-square-refinement.lisp` | Identify all four sampled sides with uniform polynomial paths; a fixed finite coarse boundary check preserves the actual grid index at every multiple mesh |
| `polynomial-certified-root-search.lisp` | One accepted coarse boundary certificate and nonzero coarse index guarantee a computed approximate root at every positive error; the fine index is derived by refinement |
| `square-cells.lisp` | Compute containing cells for every rational square point; prove closed-boundary coverage, disk bounds and cell-distance estimates |
| `polynomial-cell-clearance.lisp` | Derive a uniform polynomial variation cap on every cell; small values force retention and discarded cells exclude them |
| `polynomial-sublevel-cover.lisp` | Enumerate all retained grid cells; prove finite address bounds, exact membership, complete small-value coverage and a value bound throughout the retained union |
| `polynomial-resolved-cover.lisp` | Compute both spatial and value resolution; prove the epsilon/3-epsilon cover bounds, empty-cover exclusion and nonemptiness from a nonzero boundary certificate |
| `euler-square-cover.lisp` | Construct native Euler small-value covers from actual uniform polynomial models on local squares; prove fine-request completeness, value bounds and complement exclusion |
| `euler-square-clearance.lisp` | Generate accepted Euler value checks and positive regular charts outside a computed cover; derive uniform denominator and reciprocal bounds and accepted shifted checks |
| `positive-square-disk.lisp` | Compute a disk inside the positive half-plane containing any positive rational square; prove offset and affine-coordinate identities |
| `euler-positive-square-cover.lisp` | Translate actual Euler polynomial coefficients to physical coordinates; construct covers on every positive square with completeness, value bounds and generated complement clearance |
| `polynomial-cell-index.lisp` | Identify explicit polynomial cell and row sums with native grid indices; prove exact outer-boundary conservation |
| `polynomial-cover-index.lisp` | Prove discarded cells have zero index, so the retained cover carries the exact outer grid index |
| `polynomial-cover-search.lisp` | Compute a retained nonzero-index cell from a nonzero outer index; prove bounded search completeness and address and value bounds |
| `polynomial-indexed-cover.lisp` | Combine requested spatial and value resolution with a fixed coarse boundary certificate; preserve the actual cover index and compute its nonzero-index address |
| `euler-cell-clearance.lisp` | Generate native Euler checks, regular neighborhoods and reciprocal bounds on every discarded cell; prove model-index conservation on the actual Euler cover |
| `square-cover-circles.lisp` | Translate retained cell addresses to exact rational boxes; a finite inside/outside distance check proves a circle misses the entire cover |
| `square-circle-geometry.lisp` | Check circle containment in a square; prove exact rational circle, chart and Cauchy-orbit geometry |
| `euler-square-circles.lisp` | A finite check on the computed Euler cover generates uniform clearance, reciprocal caps and regular neighborhoods at all rational circle points and Cauchy samples |
| `polygon-perturbation.lisp` | Prove polygon index stability from pointwise perturbations and an edge budget; close paths and transport finite nearness and avoidance checks |
| `euler-positive-polynomial-stability.lisp` | Translate actual Euler models of arbitrary target degree; prove uniform polynomial and native comparisons and pointwise path bounds |
| `polynomial-square-path-control.lisp` | Control mapped polygon steps and whole segments by polynomial coefficients; prove square convexity, closure and perturbation exclusion |
| `euler-polygon-index.lisp` | One finite coarse value and coefficient certificate fixes the polygon index across Euler approximation degrees and fine requests |
| `polygon-edge-access.lisp` | Access every finite path edge and mapped value exactly; include the closing edge through explicit polygon closure |
| `euler-polygon-clearance.lisp` | Generate positive half-plane bounds for all fine models and native Euler clearance along every certified polygon segment; derive a uniform reciprocal cap |
| `euler-square-native-index.lisp` | Identify canonical square-grid and retained-cover indices with the fixed coarse Euler index; compute a retained nonzero-index address |
| `euler-native-polygon-index.lisp` | Prove exact native Euler sample indices agree across fine requests and with every admissible polynomial model on the fixed sampled contour |
| `polygon-slices.lisp` | Prove exact bounded list-slice and closure identities used to assemble finite refinement checks |
| `euler-native-edge-sampling.lisp` | Generate native Euler edge samples in a common coarse half-plane; every integer subdivision preserves the actual endpoint crossing |
| `euler-native-path-access.lisp` | Prove native value-list shape, append, exact indexed access and closure identities |
| `euler-native-refinement.lisp` | Construct all native refinement blocks and anchors; prove the refinement check and index equality across counts and requests |
| `euler-native-domain-refinement.lisp` | Identify the generated native refinement exactly with actual Euler values on the subdivided domain polygon |
| `square-line-clearance.lisp` | Transfer sampled perimeter clearance to all four square sides; prove canonical side-point bounds and step geometry |
| `euler-square-line-refinement.lisp` | Use the fixed coarse Euler certificate to preserve actual fine-model side crossing sums under every integer mesh multiple |
| `euler-native-indexed-cover.lisp` | Compute model requests and resolved meshes; preserve one native index across adaptive covers, compute nonzero-index addresses and prove native coverage and complement clearance |
| `weighted-power-sums.lisp` | Construct rational complex weighted power sums and first differences; eliminate one node exactly without a separation hypothesis |
| `power-sum-blocks.lisp` | Bound finite coefficient blocks and propagate first-order residual bounds through an entire prefix |
| `power-sum-domination.lisp` | Prove polynomial domination of every finite prefix by the first M power sums for M unit-disk nodes, including repeated nodes |
| `power-sum-reversal.lisp` | Reverse outer-node power systems exactly and control the total weight from any late block of M orders |
| `power-sum-search.lisp` | Compute a large-term index in every M-order block from nonzero total weight, with an explicit rational threshold |
| `pole-cluster-powers.lisp` | Construct positive-multiplicity cluster power systems from checked pole distances; prove positive total weight and exact logarithmic-derivative coefficient scaling |
| `pole-cluster-search.lisp` | Compute a large cluster logarithmic-derivative coefficient; identify its total weight with the finite factor model quotient and certify approximation stability |
| `zeta-pole-quadratic.lisp` | Prove pole-coefficient shifts and the exact three-neighbor identity under multiplication by s(s-1), including the normalized zeta residue's minus sign |
| `zeta-cluster-quadratic.lisp` | Prove the scaled three-coefficient identity and a rational norm budget for normalized cluster coefficients |
| `zeta-cluster-search.lisp` | Compute a large normalized zeta principal-part coefficient in M+2 orders, allowing cancellation of its initial aggregate; certify a positive threshold and an approximation margin |
| `ray-positive-scales.lisp` | Prove positive radial scaling preserves ray crossings; reconstruct a positive same-ray factor and preserve crossings at a collinear endpoint |
| `ray-triangle-signs.lisp` | Classify triangle winding by cyclic determinant signs for all origin-avoiding edges, including positive collinear edges |
| `ray-triangle-products.lisp` | Prove determinant and dot-product scaling under complex multiplication and invariance of safe triangle winding under any nonzero factor |
| `ray-generic-anchor.lisp` | Compute a guarded rational fan anchor not collinear with any vertex of a finite nonzero complex point list |
| `polygon-fans.lisp` | Define safe paths and polygons and prove exact fan decompositions of their crossing sums |
| `polygon-products.lisp` | Prove arbitrary nonzero constant multiplication preserves safe paths and polygon winding, using a computed fan direction |
| `polygon-product-checks.lisp` | Check positive half-planes on a triangular product grid; derive zero strip and triangle indices and safe diagonal edges |
| `polygon-product-index.lisp` | Prove the exact diagonal-to-boundary crossing identity and additive winding for checked pointwise products of closed paths |
| `polygon-product-budgets.lisp` | Compute a positive product-step budget from annulus bounds and prove it generates every product cell and strip half-plane check |
| `polygon-product-additivity.lisp` | Generate safe boundaries and the whole product-path check from annuli and steps; prove winding additivity at the computed step budget |
| `complex-outer-powers.lisp` | Prove exact complex power norm squares, lower norms for outer powers and the radius-two difference bound 4^k times the input error |
| `ray-power-samples.lisp` | Construct power samples on a common path; prove their shape, endpoints, annuli, uniform step bounds and pointwise product identity |
| `ray-power-index.lisp` | Compute one step budget for every exponent through a degree and prove sampled power winding equals that exponent times the input winding |
| `polynomial-square-lines.lisp` | Sample the canonical square perimeter along four lines without constructing the full grid; prove exact equality with the existing polynomial boundary values |
| `ray-path-assembly.lisp` | Preserve annulus and step certificates through finite path concatenation and reversal, with explicit endpoint join checks |
| `unit-square-boundary.lisp` | Construct the canonical unit-square boundary, prove its 1-to-2 annulus and fixed coarse certificate, and derive index one on every multiple mesh |
| `unit-square-steps.lisp` | Prove exact side sample step 2/count and assemble the entire closed square boundary with the same step budget |
| `unit-square-power-index.lisp` | Compute the square mesh from the degree; derive the monomial winding and safety certificates and preserve its index under every nonzero leading factor |
| `polynomial-monomials.lisp` | Construct actual monomial coefficient lists and prove their evaluation, path identity and canonical grid boundary index equal to the degree |
| `polynomial-leading.lisp` | Split actual coefficients into their leading term and lower list; prove polynomial concatenation and the exact leading-term evaluation identity |
| `polynomial-degree-bounds.lisp` | Prove sharp coefficient-mass degree bounds and a degree-lower remainder estimate for actual polynomial values |
| `polynomial-leading-radius.lisp` | Compute a positive rational leading lower bound and an outer radius; prove the entire lower-degree remainder is at most one sixteenth of the leading boundary scale |
| `polygon-perturbation-budgets.lisp` | Generate polygon homotopy checks from annulus clearance, closed-path step bounds and pointwise perturbation budgets |
| `ray-power-safety.lisp` | Prove sampled power paths are safe at every common mesh satisfying the computed power-step budget |
| `ray-multiplier-bounds.lisp` | Preserve annulus, adjacent-step and closure bounds under multiplication by a fixed complex factor |
| `polynomial-leading-factor.lisp` | Construct the normalized leading multiplier and its positive lower bound, upper cap and scaled-term identity |
| `polynomial-leading-comparison.lisp` | Generate pointwise comparison, annulus and step bounds for the actual rescaled polynomial and its leading monomial |
| `polynomial-outer-index.lisp` | Derive the general polynomial outer-path index from explicit rational mesh inequalities and leading-term domination |
| `unit-square-mesh.lisp` | Compute a square mesh from any positive rational step target and prove its annulus, closure, step and index-one data |
| `polynomial-outer-mesh.lisp` | Compute a positive polynomial step target and derive degree as its outer boundary index at every sufficiently fine multiple mesh |
| `polynomial-global-root-mesh.lisp` | Generate one common mesh with small-cell variation and outer grid index equal to the degree from coefficients and tolerance |
| `polynomial-approximate-root.lisp` | Compute a rational approximate root of each nonconstant polynomial with nonzero final coefficient; prove the returned address and error bound |
| `polynomial-streaming-search.lisp` | Search polynomial rows on demand, prove equality with full-grid search and transfer the approximate-root theorem to the executable implementation |
| `polynomial-division-leading.lisp` | Prove synthetic division preserves the leading coefficient, produces a nonempty lower-degree quotient and reconstructs the polynomial with its exact constant remainder |
| `polynomial-factor-budgets.lisp` | Compute positive recursive error requests and prove approximate-root, degree-decrease and preserved-input data for each factorization step |
| `polynomial-factor-roots.lisp` | Construct the terminating list of rational approximate linear factors, prove its exact degree-many length and define the rational product model |
| `polynomial-factor-error.lisp` | Propagate uniform polynomial error through one linear factor using the exact synthetic-division identity and a generated rational error budget |
| `polynomial-approximate-factorization.lisp` | Prove that the computed degree-many rational linear factors approximate the polynomial at every rational point of the requested disk |
| `polynomial-trim.lisp` | Remove trailing zero coefficients, preserve every polynomial value and certify a nonzero final coefficient whenever the trimmed list is nonempty |
| `polynomial-normalized-factorization.lisp` | Extend complete approximate factorization to arbitrary coefficient padding, constants and the zero polynomial, with normalized-degree length and uniform disk error |
| `ray-axis-crossings.lisp` | Prove exact vertical-edge endpoint potentials and zero horizontal-edge crossings, including the fixed convention at ray vertices |
| `ray-axis-paths.lisp` | Recognize constant-coordinate paths and prove that vertical crossing sums telescope while horizontal path and row indices vanish |
| `ray-translations.lisp` | Translate finite paths by a rational root, preserving their shape, endpoints, concatenation, reversal and fixed-coordinate properties |
| `unit-square-axes.lisp` | Prove that every sample on each canonical unit-square side has its exact fixed real or imaginary coordinate |
| `unit-square-translated-sides.lisp` | Construct translated-side endpoint and coordinate data and compute all four linear-factor side indices from endpoint potentials |
| `unit-square-linear-index.lisp` | Prove the translated unit-square index equals its half-open-square indicator on every positive mesh and is exactly zero or one |
| `complex-square-radius.lisp` | Define rational square radius, prove its reverse triangle inequality and compare its squared difference with the complex squared distance |
| `unit-square-clearance.lisp` | Compute exact unit-square membership and a root-to-boundary gap; prove translated annuli and preserve adjacent-step bounds under translation |
| `unit-square-linear-bounds.lisp` | Prove every canonical boundary sample lies on the unit square, compute a safe linear-factor mesh from its positive gap and preserve its zero-or-one index under nonzero leading multiplication |
| `polynomial-factor-paths.lisp` | Map complete linear-factor models along finite paths, preserve shape and closure, identify recursive pointwise products and bound the sum of linear-factor counts |
| `polynomial-factor-masses.lisp` | Compute recursive lower, upper and Lipschitz masses and prove their rationality and required signs for factor families off the unit-square boundary |
| `polynomial-factor-annuli.lisp` | Prove the computed lower and upper bounds for actual product values and generate annulus bounds for their sampled paths |
| `polynomial-factor-differences.lisp` | Prove a uniform product-value difference bound on the unit square and generate adjacent-step checks from the domain mesh |
| `polynomial-factor-step-budget.lisp` | Compute one positive domain step that meets every partial-product winding budget and both factor and tail path-step bounds |
| `polynomial-factor-winding.lisp` | Prove product winding equals the sum of zero-or-one factor indices on every sufficiently fine common mesh; compute the mesh and bound its nonnegative index |
| `polynomial-edge-clearance.lisp` | Extract positive rational slack from each existing polynomial edge check and prove value exclusion on its entire rational segment |
| `polynomial-line-clearance.lisp` | Take a positive minimum of checked edge clearances and prove a uniform line clearance with explicit subedge selection |
| `polynomial-mesh-cells.lisp` | Compute a coarse cell and local parameter for every rational line parameter and extend subedge clearance to the whole line |
| `polynomial-square-clearance.lisp` | Generate positive clearance from a coarse square certificate, cover every rational unit-square boundary point and exclude small polynomial values there |
| `polynomial-boundary-factors.lisp` | Compute complete approximate factors below the coarse clearance, prove normalized leading data and member vanishing, and derive that every generated factor root is off the boundary |
| `polynomial-boundary-factor-paths.lisp` | Prove a positive collar for the generated product and its pointwise comparison with the original polynomial along the full unit-square boundary |
| `polynomial-nonnegative-index.lisp` | Compute a shared coarse-mesh refinement, prove the product-to-polynomial homotopy and identify the original coarse polynomial index with a nonnegative factor count bounded by normalized degree |
| `polynomial-square-normalization.lisp` | Compute affine normalization of every rational square; prove exact polynomial evaluation, side and grid transport after trailing-zero trimming |
| `polynomial-normalized-clearance.lisp` | Transport the original coarse certificate's uniform clearance to the normalized unit-square polynomial and prove exact unit-side step bounds |
| `polynomial-normalization-budget.lisp` | Compute a multiple of the original mesh from normalized coefficients and inherited clearance, with a strictly smaller edge-variation cap |
| `polynomial-normalization-check.lisp` | Generate every normalized polynomial edge, line and square boundary check from the original accepted physical-square certificate |
| `polynomial-square-counts.lisp` | Identify any checked rational-square polynomial index with its normalized factor count; prove nonnegativity and the original normalized-degree bound |
| `euler-square-polynomial-check.lisp` | Prove the exact physical adjacent step and generate the base polynomial boundary checker from the existing canonical native Euler square check |
| `euler-square-counts.lisp` | Bound native square samples, all refined model grids and total retained-cover indices between zero and one fixed base-model degree; derive positivity from a nonzero native index |
| `euler-model-square-clearance.lisp` | Generate base-vertex clearance and a uniform eta/4 margin for every later Euler polynomial at every rational boundary point and fine line sample |
| `polynomial-clearance-mesh.lisp` | Compute a coefficient-based integer-multiple mesh from any positive margin; prove the edge cap is smaller and generate each physical-square edge check |
| `euler-model-square-check.lisp` | Generate an accepted polynomial square boundary checker for every Euler model request using the fixed canonical native certificate and a computed mesh |
| `unit-square-root-selection.lisp` | Compute the interior contributing roots, prove their length equals the factor count and prove strict interior membership when all factors avoid the boundary |
| `euler-model-factor-counts.lisp` | Identify the selected fine-model root count with the fixed native contour index and bound it by the fixed base-model degree across later requests |
| `euler-model-pole-candidates.lisp` | Map selected roots into strip squares with unit weights, generate valid pole families and cluster checks, and instantiate the bounded coefficient search with block length equal to the fixed native count |
| `polynomial-factor-accuracy.lisp` | Clamp an independent factor tolerance by the boundary-safe request; prove uniform radius-two disk approximation, off-boundary factors and small residual at every generated root in the disk |
| `polynomial-accurate-paths.lisp` | Generate boundary collars and pointwise factor-to-polynomial comparison for every positive independently requested factor tolerance |
| `polynomial-accurate-counts.lisp` | Compute the common refinement and prove homotopy and the same exact coarse factor count for every positive requested tolerance |
| `polynomial-square-accurate-counts.lisp` | Transport independently accurate factors and their exact count to any checked rational square; prove normalized disk approximation and physical-root residual bounds |
| `euler-model-accurate-factors.lisp` | Keep the fixed native root count across independent Euler and factor requests; prove selected-root geometry and native Euler small-value bounds |
| `euler-accurate-pole-candidates.lisp` | Generate valid strip pole candidates and cluster checks at arbitrary factor accuracy, preserve the fixed native count and bounded coefficient search, and certify small native values throughout the family |
| `polynomial-factor-coefficients.lisp` | Construct coefficients for the complete product of linear factors and prove exact agreement with factor evaluation |
| `polynomial-local-derivative-comparison.lisp` | Build the shifted and scaled polynomial difference and use its finite Cauchy cap to bound the derivative difference |
| `polynomial-accurate-derivative.lisp` | Generate the local Cauchy checks from the uniform radius-two factor approximation and obtain a derivative error of 2*epsilon on the radius-3/2 disk |
| `polynomial-factor-quotient-comparison.lisp` | Bound the factor logarithmic-derivative error using the original derivative cap and a shared denominator margin |
| `euler-factor-contour-comparison.lisp` | Transfer derivative and quotient comparisons to the normalized Euler boundary with the fixed coarse-certificate margin |
| `polynomial-affine-derivatives.lisp` | Prove exact derivative rules for constant addition, linear multiplication, trailing-zero trimming and affine substitution |
| `euler-square-derivative.lisp` | Enclose the whole physical square in a strict inner disk and compare its formal Euler derivative to the native local coefficient under a fixed cap |
| `euler-normalized-square-derivative.lisp` | Transport the derivative cap and native derivative comparison to normalized coordinates and derive the fixed-cap factor quotient estimate |
| `euler-native-factor-quotient.lisp` | Combine native value and derivative errors to bound the factor quotient against the evaluated native quotient on the whole square boundary |
| `polynomial-factor-log-sum.lisp` | Identify the product's logarithmic derivative with the sum of its reciprocal linear factors, retaining repeated occurrences |
| `euler-factor-pole-sum.lisp` | Derive uniform factor clearance and compare the complete reciprocal sum directly with the normalized native quotient |
| `unit-square-pole-split.lisp` | Split the reciprocal sum into the selected interior list and the strictly exterior list while retaining repeated factors |
| `euler-base-boundary-margin.lisp` | Preserve the fixed base polynomial margin of 3*eta/4 along every rational point on the square boundary |
| `euler-interior-root-clearance.lisp` | Compute a fixed distance from every selected root to the boundary using the base polynomial margin and Lipschitz cap |
| `polynomial-pole-sum-clearance.lisp` | Bound a reciprocal sum by the number of terms divided by their common distance lower bound |
| `euler-interior-pole-sum-bound.lisp` | Generate the selected list's boundary clearance and bound its reciprocal sum using the fixed native count |
| `euler-exterior-pole-sum-bound.lisp` | Bound the complete and complementary sums uniformly in later Euler degree and accuracy and split the native boundary comparison |
| `square-pole-coordinate-transport.lisp` | Transport the selected reciprocal sum to the same physical unit-weight pole list used by the cluster search |
| `euler-physical-pole-contour-model.lisp` | Compare the native physical boundary quotient with the selected pole sum plus the bounded exterior term |
| `polynomial-disk-factorization.lisp` | Represent complete approximate factors by coefficients and prove their value approximation on any requested disk |
| `polynomial-disk-factor-derivative.lisp` | Use the gap between two disks for finite Cauchy extraction and bound the derivative error by epsilon divided by the gap |
| `polynomial-disk-factor-quotient.lisp` | Derive factor clearance and compare the complete reciprocal sum with the original polynomial logarithmic derivative |
| `euler-circle-factor-quotient.lisp` | Factor the same global Euler polynomial used by the checked circle and compare its full reciprocal sum with the native circle value |
| `circle-pole-split.lisp` | Split rational factors by exact squared radius and characterize the strictly exterior list once boundary roots are excluded |
| `euler-circle-pole-split.lisp` | Exclude factors on the checked circle and give the native approximation by the interior and exterior reciprocal sums |
| `circle-exterior-resolvent.lisp` | Construct a rational contraction cap for an exterior factor and identify its reciprocal with a normalized resolvent |
| `circle-exterior-pole-polynomial.lisp` | Approximate a single exterior reciprocal on the whole centered disk and retain the requested coefficient exactly |
| `circle-exterior-coefficient-model.lisp` | Construct a polynomial for the exterior list with arbitrary uniform error and exact requested coefficient |
| `circle-exterior-coefficient-bound.lisp` | Compute the required circle samples and prove that their bound controls the exterior coefficient |
| `euler-circle-factor-sum-cap.lisp` | Bound the full circle factor sum by a fixed cap independent of later polynomial target and factor precision |
| `circle-interior-root-clearance.lisp` | Compute a positive common clearance for the selected circular list using its maximum squared radius |
| `euler-circle-exterior-coefficients.lisp` | Generate every required exterior coefficient check from the checked Euler circle and prove a cap valid for every coefficient of the chosen factor list |
| `circle-interior-count-resolvent.lisp` | Rewrite each weighted interior reciprocal as a conjugated geometric resolvent on the rational unit circle |
| `circle-interior-count-polynomial.lisp` | Build the interior polynomial with exact count as its constant coefficient and arbitrary uniform approximation error |
| `cauchy-real-constant.lisp` | Bound the real constant coefficient by the real parts of a computed finite set of unit-circle samples |
| `circle-count-polynomial.lisp` | Combine both factor lists in a contour model whose constant coefficient counts the interior factors |
| `circle-count-comparison.lisp` | Recover exact equality of integer counts from a finite comparison of two real contour models |
| `euler-circle-count-stability.lisp` | Generate that finite comparison using the common native Euler quotient at every sample |
| `euler-circle-count-requests.lisp` | Compute admissible tolerances at any positive request and prove the count equals the fixed base count |
| `polynomial-circle-reflection.lisp` | Reflect a conjugated polynomial on the unit circle and prove evaluation and coefficient rules for monomial shifts |
| `circle-exterior-projection.lisp` | Shift the full contour model into ordinary polynomial degrees and extract its exterior coefficients exactly |
| `euler-circle-exterior-uniform.lisp` | Prove that the full contour cap controls every exterior coefficient across admissible factor refinements |
| `circle-exterior-projection-difference.lisp` | Use a shared monomial shift to compare two exterior coefficients through their full contour sums |
| `euler-circle-exterior-comparison.lisp` | Prove exact exterior coefficient comparison across Euler models and compute a Cauchy modulus from the requested precision |
| `euler-circle-center-clearance.lisp` | Construct a fixed inner disk around a checked expansion center and exclude all outer factor roots from it |
| `euler-circle-center-native-quotient.lisp` | Compare the outer factor sum with native Euler logarithmic derivative values throughout the inner disk |
| `euler-circle-center-coefficients.lisp` | Extract the full factor-sum Taylor coefficients and compare them with the native Euler logarithmic derivative polynomial |
| `circle-factor-coefficient-split.lisp` | Split exact reciprocal coefficients at a chosen radius and transport the expansion to reflected physical coordinates |
| `euler-circle-center-split-coefficients.lisp` | Compare the reflected native log coefficient with selected poles and a uniformly bounded exterior contribution |
| `mellin-quadratic-normalization.lisp` | Clear the two rational denominators in the normalized Euler expression and bound the resulting polynomial error |
| `euler-mellin-quadratic-coefficients.lisp` | Generate finite Cauchy checks for the higher coefficients after clearing the Mellin normalization |
| `mellin-quadratic-coefficient-formula.lisp` | Identify the reflected quadratic product coefficient with the three-term Mellin coefficient expression |
| `euler-mellin-quadratic-model.lisp` | Compare the native Mellin three-term expression to the negative reflected Euler log coefficient |
| `euler-circle-mellin-coefficients.lisp` | Compare the selected poles and regular exterior coefficients with the native Mellin three-term expression |
| `unit-circle-nearby-point.lisp` | Project a rational point in the closed disk to a nearby rational unit-circle point |
| `euler-circle-interior-collar.lisp` | Compute a strictly smaller radius containing every selected interior factor |
| `circle-interior-pole-power-sums.lisp` | Construct a power-sum witness for a late interior coefficient, with a cap from the count |
| `euler-circle-joint-model.lisp` | Use a shared request for the center, contour, exact count and cluster coefficient search |
| `kernel-window-index-block.lisp` | Certify a bounded block of derivative orders for one window and one computed threshold |
| `euler-window-quadratic-coefficients.lisp` | Carry failed search to three consecutive coefficients on the checked Euler chart |
| `euler-circle-window-cluster.lisp` | Derive search success from a positive circle count and one scalar coefficient budget |
| `polynomial-exponential-decay.lisp` | Compute a threshold for every polynomial-times-geometric tail |
| `euler-circle-mellin-precision.lisp` | Compute one request that controls comparison error across every order in a fixed block |
| `circle-pole-tail-budget.lisp` | Fit a geometric tail to the inverse-polynomial cluster bound at all sufficiently large orders |
| `euler-window-quadratic-tail-budget.lisp` | Combine the weighted window mass, retained real coefficient and approximation allowance |
| `euler-circle-window-budget.lisp` | Compute the large-window threshold, precision and certified rational search address under a real coefficient bound |
| `polynomial-real-anchor-normalization.lisp` | Cancel the factor at one exactly in the anchored polynomial model and bound its numerator on larger circles |
| `euler-circle-log-at-one.lisp` | Compare a real-centered factor log derivative at one with the computed Euler constant |
| `euler-circle-empty-log-model.lisp` | Construct uniformly capped log-derivative polynomials on a checked empty Euler circle |
| `polynomial-wide-linear-inverse.lisp` | Approximate the remaining real linear inverse on any strict interior disk |
| `euler-circle-reflected-log-model.lisp` | Reflect an empty-circle log polynomial into the Mellin coordinate and compare it at one |
| `euler-circle-real-normalized-model.lisp` | Construct a normalized real-circle polynomial with a uniform geometric coefficient bound |
| `complex-cancelled-normalization.lisp` | Identify complex normalization after exact cancellation of the removable factor |
| `euler-circle-real-normalized-comparison.lisp` | Compare cancelled normalization and the polynomial product on the inner comparison disk |
| `euler-circle-reflected-native-log.lisp` | Compare the reflected empty-circle logarithm with the native log polynomial |
| `euler-circle-real-native-model.lisp` | Compare real and native normalized polynomials with a linearly scaling error |
| `euler-circle-real-native-coefficients.lisp` | Transfer the local polynomial comparison to physical coefficients |
| `euler-circle-real-native-bound.lisp` | Give the canonical height-zero coefficients a geometric bound from a checked empty circle |
| `euler-circle-pair-window-certificate.lisp` | Compute and certify a rational window witness from checked positive-count and empty circles |
| `circle-finite-radius-selection.lisp` | Choose a rational circle with explicit squared-radius separation from a finite root list |
| `circle-radial-clearance.lisp` | Convert squared-radius separation to an explicit distance from every point on the contour |
| `circle-factor-clearance.lisp` | Give a uniform polynomial lower bound on a circle that separates all finite factors |
| `circle-pair-radius-selection.lisp` | Choose compatible modulated, normalization and empty real radii for finite strip points |
| `euler-circle-factor-anchor.lisp` | Transfer finite factor clearance to a native Euler value check under an explicit comparison budget |
| `circle-factor-reflection.lisp` | Reflect inner factors with unchanged boundary norm and compare the center values |
| `circle-inner-factor-count-bound.lisp` | Bound the number of inner factors independently of polynomial degree from a finite boundary check and a center lower bound |
| `euler-circle-inner-factor-count.lisp` | Apply the uniform inner factor count bound to the actual Euler approximants at independent precisions |
| `circle-bounded-radius-selection.lisp` | Select a rational radius with a common positive gap given a bound on the number of inner factors |
| `euler-circle-bounded-radius.lisp` | Apply the common radius gap to independent Euler polynomial and factorization requests |
| `circle-reflected-factor-comparison.lisp` | Transfer a reflected product lower bound to the original factorization using only the inner count and common radius margin |
| `circle-reflected-factor-normalization.lisp` | Normalize each reflected model factor and bound its logarithm argument on the common inner disk |
| `signed-log-bounds.lisp` | Construct signed rational logarithm enclosures with overlap, reciprocal and linear error bounds |
| `signed-log-multiplication.lisp` | Prove product enclosure overlap and lower-endpoint error with independent signed logarithm requests |
| `complex-log-unit-increment.lisp` | Bound the error of the linear term for the logarithm of the squared norm of one minus a small complex input |
| `complex-log-relative-cell.lisp` | Factor the quotient of consecutive complex line samples and bound its signed logarithm increment |
| `complex-log-path-sum.lisp` | Sum finite logarithm increments on a rational line with explicit accumulated error |
| `rational-power-secant.lisp` | Prove the exact rational power secant identity and its endpoint slope bounds |
| `rational-monomial-quadrature.lisp` | Bound rational monomial rectangle sums on the unit interval by their exact primitive values and the mesh error |
| `complex-log-series-coefficients.lisp` | Build the finite logarithm coefficients and compare integrated geometric coefficients to mesh error |
| `complex-log-grid-increment.lisp` | Identify each quadrature table increment with the corresponding exact geometric row |
| `complex-log-grid-approximation.lisp` | Bound the error of replacing the finite relative path sum by integrated geometric samples |
| `complex-log-series-comparison.lisp` | Compare the signed scalar logarithm to the logarithm polynomial with explicit total error |
| `complex-log-series-precision.lisp` | Compute the truncation order, rational mesh and scalar logarithm request for any positive comparison tolerance |
| `cauchy-nonnegative-real-sum.lisp` | Bound real-weighted Cauchy sums from nonnegative real parts at the sampled points |
| `cauchy-real-part-moments.lisp` | Split the weighted real-part sum into ordinary and shifted Cauchy moments |
| `cauchy-nonnegative-real-coefficients.lisp` | Use one positive real-part check to cap any nonconstant polynomial coefficient |
| `cauchy-nonnegative-real-bound.lisp` | Turn a finite nonnegative real-part check into a uniform interior polynomial bound |
| `circle-reflected-logarithm-polynomial.lisp` | Assemble the factor logarithm series into one polynomial with zero constant term |
| `circle-reflected-square-product.lisp` | Separate the squared norms of each reflected factor and prove strict positivity on the applicable disk |
| `circle-reflected-logarithm-increment.lisp` | Compare one reflected product log-ratio increment with the normalized factor logarithm |
| `circle-reflected-logarithm-comparison.lisp` | Bound the error in the complete reflected logarithm polynomial |
| `signed-log-positive-lower.lisp` | Turn a signed logarithm lower bound into an explicit positive lower bound for its argument |
| `circle-reflected-harnack-budget.lisp` | Compute scalar bounds for the finite Harnack estimate |
| `circle-reflected-harnack-polynomial.lisp` | Construct the nonnegative-real-part polynomial model for the reflected product |
| `circle-reflected-harnack-lower.lisp` | Derive a positive interior lower bound for the reflected product from a checked squared boundary cap |
| `cauchy-boundary-geometric-bound.lisp` | Bound the coefficient list and all strict inner disk values from one finite Cauchy boundary check |
| `circle-reflected-boundary-budget.lisp` | Generate the reflected product's squared boundary cap from the original unit-boundary cap |
| `circle-factor-uniform-clearance.lisp` | Use the common radius margin and Harnack estimate to give a uniform factor-polynomial contour floor |
| `euler-circle-uniform-clearance-budget.lisp` | Compute positive Euler radius and approximation budgets before choosing either approximation precision |
| `euler-circle-uniform-anchor.lisp` | Certify a uniform native Euler anchor on the generated contour from independent fine model requests |
| `euler-disk-native-value-cap.lisp` | Bound the native Euler value uniformly on a fixed disk at every request up to one |
| `euler-neighborhood-uniform-slope.lisp` | Transfer the disk cap to the normalized local polynomial and bound its half-disk slope uniformly |
| `euler-neighborhood-uniform-radius.lisp` | Compute shared lower bounds for the Euler neighborhood and regular contour patch radii |
| `euler-circle-fixed-grid.lisp` | Build both rational charts from patches with a common local outer radius |
| `euler-circle-regular-geometry.lisp` | Bound the origin and pole distances and place all local outer disks inside the global Euler disk |
| `euler-circle-regular-grid.lisp` | Compute a grid count and prove every node with the prescribed anchor floor passes the patch check |
| `euler-circle-pole-band.lisp` | Reserve a subinterval of normalized radii with a fixed positive physical squared distance gap from the pole |
| `euler-circle-uniform-grid.lisp` | Turn the generated contour's pointwise anchor floor into a checked finite cover |
| `euler-circle-generated-cover.lisp` | Compute a radius inside the input interval and both accepted native Euler charts |
| `circle-no-inner-factors.lisp` | Apply the interior Harnack lower bound to an unreflected polynomial when the inner factor count vanishes |
| `circle-normalized-factor-model.lisp` | Rescale the same chosen physical factor list and preserve evaluations and absence of inner factors |
| `euler-physical-factor-comparison.lisp` | Compare the normalized physical factors to the original polynomial and to native Euler values |
| `euler-circle-small-value-count.lisp` | Compute an interior value threshold and force a positive factor count from a sufficiently small Euler sample |
| `euler-physical-factor-model.lisp` | Generate the center bound and boundary check for the actual physical factor model, and force a positive normalized count |
| `euler-circle-positive-count-witness.lisp` | Force the exact interior count of a checked Euler cover from a small value in a prescribed inner disk |
| `real-dirichlet-damping.lisp` | Compare the real-axis Dirichlet sample to rational exponential enclosures and prove reverse order of the damping bounds |
| `circle-interior-factor-point.lisp` | Extract a rational point strictly inside a circle where a retained factor vanishes |
| `euler-circle-interior-probe.lisp` | Compute arbitrarily small interior Euler samples from a checked positive count |
| `euler-circle-empty-count-witness.lisp` | Transfer absence of inner factors from a reference model to the exact count of a smaller checked circle |
| `real-dirichlet-order.lisp` | Prove quantitative approximate monotonicity of real Dirichlet samples and a positive first-pair gap |
| `real-dirichlet-eta-prefix.lisp` | Bound the real part of the finite alternating sum using consecutive Dirichlet pairs |
| `real-dirichlet-parity.lisp` | Split the ordinary finite prefix into its alternating and even components |
| `real-dirichlet-even-transport.lisp` | Transport the even prefix through the sample at two with a computed finite error |
| `euler-real-eta-cancellation.lisp` | Cancel the two finite Euler endpoints in the eta subtraction and bound the residual |
| `euler-real-eta-comparison.lisp` | Compare the finite eta subtraction to the native Euler continuation |
| `euler-real-eta-budget.lisp` | Compute a common truncation and primitive precision from the first-pair lower bound |
| `euler-real-nonvanishing.lisp` | Certify a positive Euler value floor at positive rational real rates away from one |
| `euler-real-axis-clearance.lisp` | Combine the eta estimate and the neighborhood at one to bound the real axis uniformly above any positive lower rate |
| `euler-near-real-clearance.lisp` | Extend the uniform real-axis value floor to a computed strip inside any real-centered Euler disk |
| `dirichlet-right-block-decay.lisp` | Normalize a sample by its positive integer index and bound it on a right-half-plane dyadic block |
| `dirichlet-right-block-mass.lisp` | Bound the sum of absolute sample coordinates on a finite block |
| `dirichlet-right-dyadic-mass.lisp` | Combine dyadic block masses with a reciprocal-square tail bound |
| `mobius-sieve-coefficients.lisp` | Construct finite Möbius weights from distinct primes and certify their range and table lookup |
| `mobius-sieve-divisor-sums.lisp` | Reindex divisor sums when adding one prime to the sieve |
| `mobius-sieve-inversion.lisp` | Enumerate the primes through a cutoff and prove exact Möbius cancellation in the finite hyperbola |
| `mobius-hyperbola-product.lisp` | Bound the common-request multiplication error in the Möbius hyperbola |
| `dirichlet-node-mass.lisp` | Identify sample-table mass on an index interval with the corresponding Dirichlet sample sum |
| `mobius-hyperbola-tail.lisp` | Bound the omitted Möbius rectangle products by two mass products and bound the weighted prefix |
| `dirichlet-right-inverse.lisp` | Combine finite divisor cancellation, tail mass and rounding into a certified inverse estimate |
| `dirichlet-right-mass-cap.lisp` | Bound the total and tail mass of a dyadic sample table to the right of one |
| `dirichlet-right-inverse-budget.lisp` | Compute a square cutoff and joint primitive request that certify ordinary dyadic prefix clearance |
| `euler-right-clearance-budget.lisp` | Combine the inverse, terminal node and continuation budgets with a computed dyadic block |
| `euler-right-clearance.lisp` | Prove native Euler clearance uniformly in height and on every closed half-plane strictly right of one |
| `euler-real-circle-probe-geometry.lisp` | Exclude near-real and rightward small probes and derive a strict horizontal radius gap |
| `euler-real-circle-checked-probe.lisp` | Use a positive real count to generate a small probe and certify that the first real band is empty |
| `euler-window-circle-cover.lisp` | Construct a checked cover in a supplied physical radius band at real part 252 |
| `euler-window-interior-sample.lisp` | Convert a physical interior disk and its small-value request to the normalized positive-count test |
| `euler-window-real-bands.lisp` | Compute the real radius gap, the band spacing and the checked covers on those bands |
| `euler-window-real-scan.lisp` | Scan from the first empty real cover to the last empty one or the first adjacent positive count |
| `euler-window-height-grid.lisp` | Compute a rational height index and prove its error and range |
| `euler-window-modulated-covers.lisp` | Construct the modulated cover and a request valid at every possible rounded height |
| `euler-window-probe-modulation.lisp` | Move an interior probe from the first positive real circle to a positive modulated circle |
| `euler-window-circle-pair.lisp` | Construct compatible paired circles and certify the positive count from a small seed-region value |
| `euler-window-ceiling-reduction.lisp` | Compute the ceiling threshold and derive a rational violation from the prepared contours |
| `euler-window-encoded-zero.lisp` | Admit arbitrarily fine rational zero probes and prove the arithmetic windowed ceiling theorem |
