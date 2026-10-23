---
title: Trust and axioms
description: Which axioms are allowed, what the comparator covers, and how the public source relates to the accepted development source.
---

# Trust and axioms

## Axioms and forbidden constructs

Allowed foundational axioms: `propext`, `Quot.sound`, and `Classical.choice`. No `sorryAx`, custom axiom, `unsafe`, or `native_decide` is allowed in the scientific modules. Challenge files contain intentionally admitted comparison statements and are not scientific proof targets. The two comparator configurations cover 108 full-tier and 12 headline slots; they do not compare every library declaration. Exact source receipts and statement comparison are distinct from manuscript-fidelity review.

## Source history and receipts

This is a fresh public source history. [Source correspondence](https://github.com/chenle02/chemotaxis-paper-iii-lean/blob/main/data/source-correspondence.json) records the single documentation-comment change to the accepted mathematical source. New release receipts bind this public commit; older private receipts are not claimed as receipts for this history. The public scope summary preserves the accepted correspondence judgments and conditions without publishing private review histories.

## What the tools check, and what they do not

- [What the checks establish](verification.html#what-the-checks-establish) and [how this was checked](verification.html#how-this-was-checked), on the generated verification page.
- [Release evidence](evidence/): the authenticated phase composite, recovery summary and logs, with their documented discrepancies.
- [Public release review](public-release-review.html).
- lean-pkg's [trust model](https://github.com/lean-pkg/lean-pkg/blob/main/docs/trust-model.md).

No tool checks that a Lean statement says what the paper says; the [results map](results.html) and the verification page put both side by side for that comparison.
