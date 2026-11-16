# Documentation, evidence, and reproducibility review

**Review record:** findings refer to the pinned pre-repair source. See [the integrated analysis](2026-11-16-deep-analysis.md) for the completed repairs and fresh execution receipts. Source line references remain pinned to that original commit.

Review date: 2026-11-16. Frozen source: `f66b9a74eecf76ce5b4ecc978879b60d17f71df7`, tree `93abb6a7ad7eec961936a601ca326a6363a43480`. Live repository identity supplied by the integrating reviewer: `Skyelabz210/Theory-of-the-One`, private. This review is of the 61 original files, before the draft marker and subsequent repairs. It does not claim to re-audit the nine external repositories cited in the manuscript.

The source presents a coherent research foundation with unusually clear distinctions between semantic integers, retained state, on-demand readout, arithmetic proof, and application evidence. Its principal remaining coherence problem is the connection between those layers: the manuscript is a dated mathematical/source survey, the imported Lean package covers a newer and partly different set of statements, and the architecture is an intended contract rather than a demonstrated production runtime. Those boundaries are largely acknowledged, but not yet mapped theorem by theorem or field by field.

The independent checks reproduced the finite arithmetic and all PNG figures. The strongest concrete defect found is stale success evidence surviving a failed reference-check attempt. The checksum and naming drift are packaging/ledger problems, not mathematical counterexamples. Deep theorem soundness and Lean semantics are the other reviewers' responsibilities; this report does not substitute for those reviews.

## Coverage and independent executions

Exact per-file paths, byte sizes, SHA-256 values, and review limits are in `coherence_file_inventory.json`.

| Group | Original files | Review performed |
|---|---:|---|
| Root `.gitignore`, `AGENTS.md`, `README.md`, `PUBLICATION_SCOPE.md` | 4 | Read in full; instruction/current-identity/architecture consistency |
| `docs/*.md` | 6 | Read in full; definitions, sources, application claims, local navigation |
| `evidence/` | 9 | Parsed/read; checksum recomputation, receipt source binding, original/current distinctions, historical log/JSON reconciliation |
| Thesis packet | 24 | Both Python files and packet README read in full; source JSON and metadata parsed; all figures regenerated; every PNG inspected; manuscript methods/architecture/evidence/roadmap/citations read and full claim/heading scan, with deep proof assessment delegated |
| `formal/universal/` | 17 | Build/checker/package metadata read; 11 formal module hashes and theorem-query inventories verified; smoke source read in full; semantic proof review and compilation delegated |
| `tools/run_reference_checks.py` | 1 | Read in full; success reproduction and isolated early-failure fault injection |

No production source was edited by this worker. Every execution that produces files used a separate scratch copy. Two generated formal receipts appeared in the frozen directory during the parent's build; they are excluded from the original 61-file inventory.

| Check | Result and scope |
|---|---|
| Supplied arithmetic checker, Python 3.12.14 | Exit 0; **821,881 assertions, zero failures**; output JSON exactly equals both committed reference receipts |
| Publication manifest | **59/60** entries match; sole mismatch is root README, consistent with source-head title edit |
| Current thesis packet manifest | **23/23** entries match |
| Original historical packet manifest | **21/23** match current files; README and manuscript differ exactly as editorial history says they should |
| Historical formal module hashes | **11/11** match receipt; receipt lists 130 theorem declarations |
| Historical formal log versus JSON | All **130** name/axiom rows match the structured report |
| Declared theorem versus axiom-query names | All current modules have matching name sets; order differs harmlessly in ResidueAlgorithms |
| Local Markdown file links | **25 targets checked, zero missing targets**; fragments and external URLs were not independently fetched |
| Figure regeneration | Exit 0; **8 PNG, 8 SVG, 22 definitions, 269 unit circles**; all 8 PNGs are byte-identical to committed originals |
| Figure quantitative metadata | Identical after separating the old manual visual-review/dimension fields |
| Figure visual inspection | All 8 PNGs inspected directly; no visible label clipping, caption/arrow collisions, or count inconsistency found |
| Early-failure fault injection | Wrapper exits 1 and writes failure receipt, but original code leaves old PASS arithmetic report in `evidence/current/` |

The parent reports a fresh pinned Lean build, axiom audit, Lake build and executable smoke run. Those results belong in the integrated report with the parent's exact logs; they are not independently executed by this worker.

## Ranked findings

### C1 — Medium: a failed run leaves contradictory current evidence

Location: `tools/run_reference_checks.py:22-35`, particularly conditional report copy at lines 25-26.

After a previous successful run, if the checker crashes before producing its JSON, the wrapper rewrites `execution.json` with a failed exit code and rewrites the log but leaves `residue_core_verification.json` untouched. The resulting current directory contains a new failed attempt alongside an old PASS result. The wrapper itself correctly returns nonzero; the defect is stale evidence, not a false exit status.

Reproduction was performed only in `audit_work/coherence_reference_run`: first execute the unchanged source successfully, then replace only that scratch checker's body with an immediate `RuntimeError` and rerun the unchanged wrapper. Observed exit: 1; execution receipt source hash: the injected file; remaining arithmetic report status: PASS with the original source hash. Witness: `coherence_stale_receipt_failure.json`.

Fix: invalidate the previous current report before execution, or atomically publish a complete per-run bundle that includes result availability and run identity. A failed attempt with no generated report must not retain a report presented as its own current result. Preserve historical successes in dated history if useful. The integrating reviewer reports that the bounded invalidation repair is now implemented and independently rerun: successful arithmetic remains 821,881/0, and injected early failure leaves no stale PASS report. This finding records the original-source defect; final repair evidence belongs in the integrated audit.

### C2 — Medium: live identity, visibility, and evidence freshness differ from current-facing prose

Locations: `PUBLICATION_SCOPE.md:1-11`; `evidence/STATUS.md:3,9,11`; `README.md:73`; `docs/SOURCE_RECONCILIATION.md:1`; `docs/SOURCES.md:10`; `formal/universal/README.md:5`.

The original source still names `Skyelabz210/configurable_residue_arithmetic_machines`, calls the repository public, and says no fresh Lean compilation was performed because the compiler was absent. The old preparation statement was true of the November 15 preparation, but current-facing status should reflect the renamed private draft and newly executed audit. The manuscript has a better dating boundary at lines 23 and 862: original research claims refer to the November 11 snapshots. Preserve that historical boundary rather than changing the manuscript's old research history to pretend it performed a later build.

Fix: name the current private repository in status/scope, explicitly date prior publication decisions as history, add fresh audit results and source head, and keep historical compiler receipts immutable. Do not imply a later private setting retracts earlier copies. No visibility change is required for this repair.

### C3 — Medium: the publication manifest drifts after normal edits and reruns

Locations: `evidence/PUBLICATION_SHA256SUMS.txt`, root README entry; `tools/run_reference_checks.py:29,35`; `formal/universal/check_proofs.py:87,115`.

The root README currently hashes to `e924a161960afba7b7c0ea60350f26ae1398b5ed12d6ad2006917e7fff96b8c8`; its manifest entry expects `fec1c09793c5c4a7b91494d3aebf19fa609b5a00eca9b644e95df9911065fdef`. Every other publication entry matches. This is consistent with the user editing the README title after the manifest was generated. It is not unexplained mathematical-source drift.

More generally, a legitimate wrapper rerun changes the execution timestamp, while the publication manifest includes that receipt. Lean verification writes two new unlisted receipts beside the source. A reader is not told whether the manifest certifies an immutable release snapshot or an always-current working tree.

Fix: state manifest scope and the procedure for regeneration. Include fresh current evidence, then regenerate the manifest after all final edits and execute its verification. Avoid self-reference by excluding the manifest itself. Keep original packet and historical formal hashes separate. A whole-tree hash cannot be made evergreen when its contents intentionally change.

### C4 — Medium, architectural interpretation: absence of a K field is narrower than the current storage contract

Locations: `AGENTS.md:15`; `docs/ARCHITECTURE.md:7-9`; manuscript `theory_of_the_one.md:47,658,700`.

The architecture forbids persistent scalar magnitude, including an equivalent payload concealed in metadata. The manuscript's description of the inspected external `cram-substrate` source says its retained bound is initially equal to the supplied value. That is an exact value in a metadata field at construction. Yet the claim register summarizes the compact model mainly as deriving winding rather than storing scalar K.

This is a mismatch between the breadth of the current contract and the narrower implementation evidence emphasized by the claim register. It does not invalidate the residue identity, and this worker has not freshly inspected that external implementation. The manuscript itself supplies the observation from which the conformance concern follows.

Fix: explicitly mark that inspected model as lineage/reference evidence with unresolved bound-storage conformance. State which declared bounds may depend on a public domain and which would encode the exact protected value. To certify an implementation, trace constructor, operation, cache, serialization and egress fields. Mathematical X/K variables, scalar reference oracles, and legitimate on-demand observations remain allowed; eliminating them from proofs would be an incorrect response.

### C5 — Medium, explanation/coverage: the 14 written theorem sections and 130 formal declarations need an explicit correspondence

Locations: root `README.md:27,42-46`; `formal/universal/README.md:13-24`; manuscript `theory_of_the_one.md:660,693-715,856`.

The manuscript's next steps still list signed division, shared-factor anchors, interval selection and target-resolution formalization as future work. The imported universal package contains substantial later work on these topics. This is not necessarily a contradiction: the manuscript explicitly preserves its earlier scope, and a formal theorem with a similar name need not have the manuscript theorem's exact hypotheses. However, a reader currently has to perform that comparison manually. Neither the 821,881 assertion count nor 130 Lean declaration count means all 14 prose theorem sections have been formalized verbatim.

Fix: add one claim-to-symbol matrix giving theorem number, exact Lean symbol(s), domain/hypothesis differences, current compilation status, finite check categories, and residual gap. Mark future steps as complete, partial, or open only after checking statements. Include generalized CRT/unit-orbit, compatible completion, typed heterogeneity, representation quotient and the global composition theorem even where no Lean counterpart exists; omissions are meaningful coverage gaps rather than failed theorems.

### C6 — Low/medium: the documented default proof route omits the executable smoke source

Locations: `formal/universal/check_proofs.py:18-21`; `formal/universal/lakefile.toml:3,7`; `formal/universal/ClosureSmoke.lean:25-56`; root `README.md:56-63`.

Neither the checker module list nor the default Lake roots include ClosureSmoke. A reader following the root reproduction command obtains proof compilation and axiom inspection but does not execute the comparison/divmod/GCD smoke fixtures. That is consistent with the command's stated proof purpose, but makes executable coverage easy to overlook. The smoke file includes exhaustive small frames, wide fixtures, exhausted-fuel refusal, alias behavior and reversed-orientation controls; it deserves a discoverable separate command and receipt.

Fix: document the separate smoke command after the proof build and distinguish pair checks from standalone controls. The parent has already executed it; recording the command in reproduction documentation closes the immediate usability gap without changing theorem sources.

### C7 — Low, checker hardening: axiom-query coverage is checked by count rather than identity

Location: `formal/universal/check_proofs.py:78-81,92-93`.

The script requires equal numbers of theorem declarations and distinct `#print axioms` queries and checks that compiler output matches the requested queries. It does not require each declared theorem to be one of those queries. In a future edit, an omitted new theorem could be masked by a query for an already imported theorem, preserving counts. The current files do not exhibit this defect: an independent declaration/query name-set check agrees for every module. The kernel still checks compiled proofs; this finding concerns the advertised exhaustive transitive-axiom coverage.

Fix: compare fully resolved declared theorem names with query names, or derive the inventory from Lean's environment. Do not assume source order must match; current ResidueAlgorithms queries two theorems in a different order. If extending syntax support, account for namespaces, qualified declarations, attributes and alternative theorem forms rather than relying on a broader count regex alone.

Related low-priority ledger detail: `check_proofs.py:108-111` hard-codes historical baselines 9 and 75 for old/new count fields. Those should be documented as baseline metadata, not silently treated as current semantic coverage when the source library evolves.

## Reproducibility observations and smaller friction

- The figure generator's display floating point is explicitly permitted and does not contradict integer arithmetic in the reference checker. The main checker was inspected and actually uses exact integer arithmetic. Its AST check only establishes absence of float literals and `/` syntax in that file; it is not a general runtime ban on every possible float-producing call or imported API. The current prose usually phrases this narrowly and should keep doing so.
- `build_thesis_figures.py:46-48` leaves Matplotlib SVG date and generated identifiers nondeterministic. All eight regenerated PNGs nevertheless matched byte for byte in this environment, and all quantitative metadata matched. For portable figure reproduction, record Matplotlib 3.10.8, relevant font/environment versions and optional deterministic SVG settings. This is packaging improvement, not an arithmetic error.
- `build_thesis_figures.py:369` regenerates quantitative metadata and drops the original manual `visual_review` and `render_dimensions_pixels` additions. That is appropriate unless the new images are inspected again: a historical visual attestation must not be copied forward as though it reviewed changed pixels. Document this boundary or store visual review as a separate, image-hash-bound receipt. The current worker directly inspected every original PNG, and byte-identical regeneration independently supports those exact PNGs.
- `docs/SOURCES.md:9` cites a moving `main` README link plus a content blob identifier. The blob helps identify content, but an immutable commit URL and retained source snapshot would make reproduction simpler. In contrast, the manuscript's nine repository versions and source links are commit-pinned and internally consistent.
- The nine external source repositories, original archives, DOCX/PDF, working notes and historical Greek edition are cited or intentionally retained separately. Their absence from the local tree is explicitly disclosed. This review has not treated those external materials as reverified current implementations or newly authenticated primary historical sources.
- The root guides properly distinguish RNS as established computer arithmetic from the author's particular research organization and machine design. The useful contribution should be argued through state, observation, operator, and execution contracts, not through claiming residue arithmetic itself has no prior discipline.
- A small glossary would reduce onboarding friction for shell, anchor, phase, winding, carrier, dependent view, admitted window, scalar-compatible state and heterogeneous product state. Those terms are mostly defined where used but cross-document navigation asks the reader to retain several names for closely related observation concepts.

## What the repository already does well

1. The four-layer source-to-derivation-to-machine-to-application chain is intelligible and protects both the author's research method and mathematical rigor. It lets Euclid remain the starting text while naming modern definitions and engineering choices explicitly.
2. Exact observability gives a reusable way to specify what information a query needs. It can support compiler interfaces, partial-information APIs, distributed consistency checks and abstraction/refinement reasoning, subject to constructive and cost obligations.
3. Reduced anchor/target resolution and LCM treatment of overlapping views prevent wasted or double-counted information. They offer concrete arithmetic design questions rather than a blanket promise of arbitrary expansion.
4. Distinct division contracts preserve legitimate shared-factor quotient routes while refusing to conflate them with modular inversion. That is directly useful for exact rescaling and constrained arithmetic implementations.
5. Scalar-compatible versus heterogeneous product-state semantics, source/epoch binding, and different meanings of reversibility are separated. Those distinctions are essential to avoiding apparently plausible but semantically wrong application claims.
6. The proof package is small, pinned and free of external Mathlib dependencies; source hashes, axiom receipts and negative controls make audit practical. The finite checker openly declares its oracle role and limitations instead of masquerading as a production runtime.

These benefits are supported by the repository's organization and tested artifacts. They do not establish a performance advantage, new historical priority, encryption security, continuum theorem, or whole-system integration.

## Recommended sequence

1. Finish current draft/status/identity corrections, fresh execution evidence, stale-report invalidation, and final hash verification. Retain original receipts with explicit dates.
2. Publish the precise manuscript-to-Lean coverage matrix and source-bound interpretation of what the passed proofs establish. The passed compiler result is most valuable when readers know each theorem's premises and exclusions.
3. Specify one admitted runtime state and its actual producer/source/epoch/range binding. Separate public domain bounds from value-encoding metadata. Trace all retained and serialized fields against the architecture before claiming implementation conformance.
4. Connect one bounded operation chain to that state, including admissible inputs, intermediate bounds, failure/refusal, output meaning and on-demand readout lifetime. Use the existing arithmetic and smoke oracles as independent reference evidence.
5. Once the real path conforms, measure its setup, readout, arithmetic, memory and bit-complexity costs under matching parameters. Then instantiate application-specific claims one domain at a time.

The deepest remaining work is the bridge from arithmetic statements to an authentic, bounded, compositional machine state. The current mathematical layer can be useful independently while that bridge is completed.
