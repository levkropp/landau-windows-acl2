## 00:00:00 — A proof checked in Lean

A proof of the Riemann hypothesis has recently been checked in Lean. Independent programs have accepted the formal proof. It concerns one of the most famous questions about the pattern of prime numbers. That is a remarkable development. But it leaves another question. How much mathematical machinery does this particular argument really need? To explain what Landau Windows ACL Two is trying to do, we need to look at the foundations underneath a proof.

## 00:00:29 — Peano arithmetic: rules about whole numbers

Start with the whole numbers. Zero, one, two, three, and so on. Peano arithmetic is a precise system of rules about those numbers. It tells us how the next number works, and how addition and multiplication behave. It also gives us induction. Imagine a row of dominoes. Establish the first case, then show that whenever one case holds, the next one holds too. Together, those two steps prove the property for every whole number. We never have to check the numbers one at a time. Arithmetic can also encode finite lists, fractions, and the steps of a calculation. So this small starting point can express a surprising amount of mathematics.

## 00:01:12 — ZFC: a larger mathematical framework

Now give ourselves a larger framework. ZFC is a standard collection of rules for set theory. A set is a collection of mathematical objects. The rules let us build new sets, work with infinite sets, and develop a great deal of ordinary mathematics. Even the whole numbers can be built out of sets. We can start with the empty set, then build a sequence representing zero, one, two, and so on. Inside this framework we can also construct functions, real numbers, and spaces. That is one reason ZFC is stronger than Peano arithmetic. It can describe and justify much more than the arithmetic rules alone.

## 00:01:53 — Gödel's second incompleteness theorem

Why does the strength of the rules matter? First, we need a word: consistency. A consistent system never proves a contradiction, such as zero equals one. Checking a particular proof is a finite task. But saying that no proof of a contradiction exists is a statement about every possible proof. There is a remarkable connection here. A finite proof can itself be encoded as a whole number. That lets arithmetic make statements about proofs. In nineteen thirty one, Gödel established his second incompleteness theorem. Under its usual conditions, a consistent system with mechanically specified rules and enough arithmetic cannot prove its own formal consistency. This applies to Peano arithmetic, and to ZFC. So a system can check individual arguments without being able to establish, from its own rules, that those rules will never produce a contradiction.

## 00:02:49 — How ZFC proves PA consistent

A stronger system can sometimes provide that justification for a weaker one. Here is how ZFC does it for Peano arithmetic. It constructs the whole numbers, together with addition and multiplication, and checks that they satisfy the arithmetic axioms. This is called building a model: a mathematical world where the rules hold. Valid proof steps preserve truth in that world. So an arithmetic proof cannot lead from those rules to a contradiction. That gives a proof of the consistency of Peano arithmetic, carried out inside ZFC. The justification depends on the stronger framework. When ZFC asks about its own consistency, Gödel's limit still applies.

## 00:03:32 — An assumption beyond ZFC

Now repeat that idea one level higher. Not all infinities have the same size. An inaccessible cardinal is a special size of infinity with a useful feature for our story. If one exists, the sets below it form a mathematical world satisfying ZFC. So assuming such a cardinal exists gives us a way to prove that ZFC is consistent. But we just met the obstacle. If ZFC is consistent, it cannot prove its own consistency. Therefore it cannot prove that an inaccessible cardinal exists, either. If it could, the model we just described would supply the forbidden consistency proof. Accepting an inaccessible cardinal is therefore an additional assumption beyond ZFC. This is why reducing the assumptions behind a theorem is a meaningful mathematical goal. We want to understand exactly how much of this larger framework the argument actually needs.

## 00:04:29 — What does this proof actually need?

A proof of the Riemann hypothesis has now been checked in Lean. The usual set theoretic models of Lean's universe hierarchy use ZFC together with inaccessible cardinals. Yet the Riemann hypothesis itself can be stated entirely in terms of whole numbers. The larger proof draws on substantial mathematics developed in that stronger setting. We have focused on one essential part: the classical Landau bridge. This encoded windowed ceiling reduction has now been proved in Peano Arithmetic and certified in vanilla ACL2. The direct arithmetic proof establishes this Landau conversion with fewer foundational assumptions than Lean's ambient framework. This is the result of Landau Windows ACL Two.

## 00:05:15 — The three-step picture

To see which piece we are studying, return to the picture from the original video. The dots are zeros of the zeta function, and the Riemann hypothesis puts them on the central line. There is a mirror symmetry. An off-centre dot on the left would have a partner on the right. So ruling out dots on the right is enough.

## 00:05:36 — The Landau bridge

Now watch the gap: the difference between a weighted prime count and its prediction. If a zero sits too far to the right, it contributes an oscillation that grows too quickly. That extra wave rises and falls. Eventually it would drive the gap above the allowed level. Now suppose we could prove an upper bound that the gap never crosses. Then that troublesome zero could not be there. We only used a ceiling; a matching lower bound was unnecessary. Landau's theorem makes that reasoning rigorous. In the larger proof, another argument supplies the ceiling. This connection between a one sided bound and a zero free region is the bridge we want to extract.

## 00:06:19 — The part we are extracting

Here is the piece we have extracted. Landau takes a bound on the prime counting error and converts it into a statement about zeros. We have proved the encoded ceiling conversion in Peano Arithmetic and certified the corresponding development in ACL2. The input ceiling still has to be established separately. The theorem computes a window threshold and returns a certified rational violation under its stated zero hypotheses.

## 00:06:46 — A finite witness inside a window

Our version only gets the ceiling on recurring stretches of the number line, called windows. A zero in the forbidden region must eventually force a violation in sufficiently large windows. The effective theorem should compute where that violation happens, and certify it with exact bounds. So the goal includes both finding a witness and proving that the search succeeds under the intended hypotheses.

## 00:07:12 — ACL2: computation and induction

We used ACL2, a proof system based on a computational logic for applicative Common Lisp. Common Lisp is its programming language. The foundational issue is the logical rules used by this proof. Our calculations use finite lists, exact fractions, and recursive functions whose properties are proved by induction. The corresponding development is certified in vanilla ACL2. A direct manuscript proof derives the encoded theorem in first-order Peano Arithmetic, including its threshold and rational witness. The manuscript supplies the mathematical proof, while the ACL2 certificates record the machine-checked development.

## 00:07:52 — landau-windows-acl2

That is what Landau Windows ACL Two has accomplished. The encoded ceiling reduction now has a direct Peano Arithmetic proof, a computed threshold, a certified rational witness, and its connection to the original Landau theorem. This encoded windowed Landau ceiling reduction is proved in Peano Arithmetic. Landau was our starting point. Other parts of the larger argument may also be reducible to Peano arithmetic. Whether a full arithmetic proof of the Riemann hypothesis can be found remains a separate question. This project does not settle those wider questions. Here we have completed one essential conversion, with its hypotheses and interpretation written down. The same result, with fewer assumptions.
