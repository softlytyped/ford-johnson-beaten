# The Ford–Johnson algorithm, no longer unbeaten for less than 47 elements

Lean 4 formalisation of H. G. Sager's
*[The Ford–Johnson algorithm, no longer unbeaten for less than 47 elements](note.pdf)*
([LaTeX source](note.tex)).

| Elements | Proved sorting bound | Ford–Johnson count |
| ---: | ---: | ---: |
| 26 | 90 | 91 |
| 46 | 194 | 195 |

## Build

Install [elan](https://github.com/leanprover/elan) and Python 3.10 or later, then run:

```sh
make verify
```

Lean 4.33.1 is pinned. There are no external packages. The build embeds the
compressed certificates and checks both complete trees with `native_decide`.
Allow a few minutes for the first build.

## Proof

Start with [`FordJohnson/Theorem.lean`](FordJohnson/Theorem.lean).
Its `main_theorem` states:

```text
S(26) ≤ 90,  S(46) ≤ 194,  F(26) = 91,  F(46) = 195,
S(n) ≤ F(n) − 1  for 26 ≤ n ≤ 32 and 46 ≤ n ≤ 64.
```

The proof follows the paper: `66 + 24 = 90`, `171 + 23 = 194`, then binary
insertion. `S(n)` is the least height of a sorting decision tree, defined in
[`Lib/Sorting.lean`](FordJohnson/Lib/Sorting.lean). A tree sorts when inputs
reaching the same leaf have the same relative order.

[`Lib/MergeInsertion.lean`](FordJohnson/Lib/MergeInsertion.lean) proves the
pairing, recursive sorting, and bounded insertions used for the 21- and
42-element bounds. [`Lib/BinaryInsertion.lean`](FordJohnson/Lib/BinaryInsertion.lean)
proves binary search and insertion; [`Lib/Composition.lean`](FordJohnson/Lib/Composition.lean)
proves that a sorting tree and an insertion tree compose, including relabelling
the sorted chain. These proofs are checked by Lean's kernel.

[`Lib/Certificate.lean`](FordJohnson/Lib/Certificate.lean) proves the certificate
checker sound. [`Data/Certificates.lean`](FordJohnson/Data/Certificates.lean)
checks both complete trees with `native_decide`: five elements into 21 in
24 comparisons, and four into 42 in 23. Only these two evaluations trust Lean's
native compiler and runtime. `Check.lean` checks the theorem's type and rejects
axiom dependencies beyond these evaluations and Lean's standard logical axioms.

The certificate files are preorder trees: `x y` is a comparison, with its
`x < y` branch first; `.` is a leaf. The generator preserves this tree,
encoding comparisons as the two ASCII characters `65 + x`, `65 + y`.
The archives and their hashes are in [`Data`](FordJohnson/Data).
The generated `T21.lean` and `T42.lean` files are excluded from Git.

Citation information is in [`CITATION.cff`](CITATION.cff). The repository is
archived on Zenodo at
[doi:10.5281/zenodo.23645923](https://doi.org/10.5281/zenodo.23645923).

## Licence

Copyright 2026 H. G. Sager.

The Lean code, scripts, and certificate data are licensed under the
[Apache License 2.0](LICENSE). The paper, [`note.tex`](note.tex) and
[`note.pdf`](note.pdf), is licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
