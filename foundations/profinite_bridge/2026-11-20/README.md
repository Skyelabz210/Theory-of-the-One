# CRAM arbitrary moduli and the profinite bridge

Research snapshot prepared for Anthony Diaz on 20 November 2026. This directory
collects the two completed papers, their editable sources, the first paper's
figure, and reproducible finite arithmetic evidence. The intended repository
location is `foundations/profinite_bridge/2026-11-20/` in
`Skyelabz210/Theory-of-the-One`.

## Papers and source files

| Directory | Contents | Status |
|---|---|---|
| `whitepaper/` | *Arbitrary Moduli in CRAM*, PDF, DOCX, Markdown, compatibility figure, document builder, and reproduction archive | Delivered 17-page paper; final PDF and DOCX preserved byte for byte |
| `profinite_bridge/` | *The Profinite Bridge*, revised PDF, DOCX, Markdown, and document builder | Delivered 15-page paper; final PDF and DOCX preserved byte for byte |
| `whitepaper_checks/` | Central exact-integer sweep and its recorded results | Finite arithmetic corroboration; replayed during packaging |
| `github_arbitrary_verification/` | Two pinned NINE65 scripts, their recorded outputs, and a normalized source/run manifest | Pinned source copies preserved byte for byte; replayed during packaging |
| `profinite_bridge/evidence/` | Exact finite examples, pinned packet-check source, targeted replay, and execution provenance | See that directory's README and result files for the precise scope |

Open the manuscripts here:

- [Arbitrary Moduli in CRAM — PDF](whitepaper/Arbitrary_Moduli_in_CRAM.pdf),
  [DOCX](whitepaper/Arbitrary_Moduli_in_CRAM.docx),
  [Markdown](whitepaper/Arbitrary_Moduli_in_CRAM.md).
- [The Profinite Bridge — PDF](profinite_bridge/The_Profinite_Bridge_Revised.pdf),
  [DOCX](profinite_bridge/The_Profinite_Bridge_Revised.docx),
  [Markdown](profinite_bridge/The_Profinite_Bridge_Revised.md).

The first paper's delivered reproduction ZIP is retained because its reference
[18] cites that artifact. Its useful contents are also available as ordinary
files in this directory. The ZIP's original README states Python 3.8; use
**Python 3.9 or later** for the complete check set because the pinned
dependent-sister script uses `math.lcm`. The staged archive-builder copy fixes
that minimum-version note.

## Evidence and proof status

The papers distinguish mathematical arguments, inspected formal sources,
historical compiler receipts, finite execution, and production conformance.
Those distinctions also apply to this package.

| Claim or artifact | Evidence supplied | Limit |
|---|---|---|
| Generalized anchor recovery, exact target admission, and dependent sister relations | Explicit mathematical arguments in the first paper; supporting pinned source references | A paper proof is not a new proof-assistant build |
| Historical integer and coupled-anchor Lean results | The first paper identifies matching source hashes and archived 28- and 19-declaration receipts | These are inspected historical results; packaging did not recompile those modules |
| Central arithmetic identities | 6,246,650 exact-integer cases, all passing | Finite corroboration, with the domains and oracle assumptions stated in `results.json` |
| Pinned arbitrary-moduli witness | Corrected formulas pass; old sign and modulus errors are intentionally exposed | Exit zero means the measured outcomes match the witness, not that every old claim was true |
| Dependent sister example | All 11,011 pairs at moduli 77 and 143 checked; 1,001 compatible pairs and common-polynomial updates | The example does not prove arbitrary heterogeneous operators preserve compatibility |
| Bridge finite examples | 60,093 exact assertions, including all 30,030 S6 states and the eleven partitions of six | Finite reference evidence; source integers are test oracles |
| Pinned packet identity | Original 9,000-case RNG warmup executed, followed by all 18,000 targeted Q2 cases; zero violations and 18,000 containment successes | Other archived experiments were not rerun; the selected statements and RNG advancement are preserved |
| Profinite completion, cofinal refined star family, reduced character order, and coefficient transform | Mathematical constructions and conditional proofs in the revised bridge paper | No new Lean compilation of the topological or analytic statements is claimed |
| Mock-specific analytic shadow correspondence | Defined as a further research question with explicit missing maps and operators | An arithmetic observation requirement is not identified with an analytic shadow by terminology or duality alone |

At this research-snapshot stage, the upcoming Lean work is the **exact
coefficient, refinement, and evaluation layer**, connected to the finite
observation arithmetic. This package does not claim a complete formalization of
mock theta functions, radial asymptotics, harmonic Maass completions, or analytic
shadow correspondence. It also makes no new runtime-conformance, performance, or
cryptographic-security claim.

No new Lean proof files or placeholder proof stubs are included in this research
snapshot. The finite check scripts contain executable checks and failure paths;
their passing output is not a substitute for a stub-free Lean build. Any later
formalization should report its own source revision, compiler run, and axiom
audit independently of this archive.

The semantic integers and quotients used in these proofs and test oracles do not
prescribe stored scalar winding, scalar reconstruction in the runtime, or a
replacement of the selected primary basis.

## Reproduce the first paper's checks

The checks use the Python standard library and exact integer arithmetic. Run
from this directory with Python 3.9 or later:

```sh
mkdir -p .reproduced
python3 whitepaper_checks/verify_arbitrary_moduli.py --output .reproduced/central_results.json
python3 github_arbitrary_verification/witness_arbitrary_moduli_claims.py
python3 github_arbitrary_verification/dependent_sister_probe.py --output .reproduced/dependent_sister_results.json
```

Expected central counts are 641,600 arbitrary-anchor quotient queries, 962,400
direct target projections, and 4,642,650 bounded residue-derived projections:
6,246,650 cases and zero failures. The direct projection suite uses an oracle
Euclidean quotient. The bounded suite derives a temporary quotient from residue
observations and a declared interval. The minimal target requirement is proved
algebraically in the paper; these projection checks use the sufficient quotient
modulo the target.

The witness includes 50,000 seeded projection samples and 48 star-family cases.
It verifies the corrected adjacent-anchor sign in 100 cases and deliberately
reports the erroneous historical formulas. The dependent-sister probe also
checks a mismatched-update negative control, specified multiplicative orders,
and a finite linear-root enumeration.

The recorded central run used Python 3.12.14. Interpreter-location and Python
version fields can differ on another machine; compare mathematical domains,
counts, and failure fields instead of requiring byte-identical output.

For the bridge's finite examples and packet replay, use the commands and source
pinning in [its evidence README](profinite_bridge/evidence/README.md). The packet
replay is targeted; it is not a claim that every experiment in the archived
source file was rerun.

## Rebuild the documents

The document builders resolve inputs relative to their own paths. They generate
their own `reference.docx`; no external template or workspace path is required.
The first builder also regenerates `compatible_residue_states.png`.

The observed document toolchain was Python 3.12.14, Pandoc 3.1.11.1,
python-docx 1.2.0, Matplotlib 3.10.8, and NumPy 2.3.5. Install the recorded Python
dependencies from `requirements-docs.txt`, install Pandoc separately, and supply
Liberation Serif, Liberation Sans, Liberation Mono, Latin Modern Math, and
DejaVu Sans fonts. The exact dependency pins were observed with Python 3.12;
they are separate from the lower Python requirement for the arithmetic scripts.

On a working copy, the following commands regenerate the DOCX files in place:

```sh
python3 -m pip install -r requirements-docs.txt
python3 whitepaper/build_whitepaper.py
python3 profinite_bridge/build_bridge.py
```

A locally installed LibreOffice command-line converter can create PDFs:

```sh
mkdir -p .reproduced/pdf
soffice --headless --convert-to pdf --outdir .reproduced/pdf whitepaper/Arbitrary_Moduli_in_CRAM.docx profinite_bridge/The_Profinite_Bridge_Revised.docx
```

The delivered PDFs were produced by LibreOfficeDev 26.8.0.0.alpha0 and visually
checked at 17 and 15 pages respectively. Font and renderer differences can
change pagination. A rebuild should be visually reviewed; regenerated DOCX,
PNG, ZIP, or PDF bytes need not match the preserved deliverable hashes.

The first paper's historical-format reproduction archive can be regenerated
with `python3 whitepaper/package_reproduction.py`. This overwrites that archive
in the working copy and incorporates the staged documentation corrections.

## Provenance and packaging changes

The first paper reviewed NINE65 revision
`64c1c89b191093dc12cf81b87da5fb1a02c46dc1` and Theory of the One revision
`b4c41726b28f224fc042280a4be2327b08e8365a`. Each paper supplies its own complete
references, including primary mathematical literature and access-controlled
Drive source links. Source links do not imply copies of the Drive documents are
included here.

`manifest.json` inventories the package with SHA-256 digests, origins, and
packaging transformations. The only changes to the first paper's copied scripts
are documentation-only portability corrections: the central sweep's example
command now uses `python3`, and the archive README now states Python 3.9.
The pinned repository scripts and both document builders are unmodified.
The historical run manifest's output paths are relative to its directory.

QA page images, obsolete renderings, temporary reference documents, renderer
probes, document-storage metadata, and local storage helper code are excluded.
The final PDF, DOCX, Markdown, first-paper figure, and delivered reproduction ZIP
retain their original bytes.
