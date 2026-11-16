THEORY OF THE ONE — PROOF AND SOURCE PACKET
Anthony Diaz (Acid) | Foundational research draft | 11 November 2026

CONTENTS
- theory_of_the_one.md: complete editable manuscript source, including all 14 theorem sections, the complete supplied English list, and edition-identified Greek.
- verify_residue_core.py: standalone mathematical reference checker (Python 3.11+; standard library only).
- residue_core_verification.json: recorded execution receipt: 821,881 assertions, zero failures.
- source_versions.json: exact inspected repository heads and scope.
- build_thesis_figures.py: portable generator for the eight figures; requires matplotlib. Run from any directory; output is figures/ beside the script.
- figures/: 300-dpi PNGs, SVGs, and exact counted-diagram metadata.
- SHA256SUMS.txt: checksums of all packet contents, excluding this checksum file itself.

REPRODUCE THE MATHEMATICAL CHECKS
Run: python3 verify_residue_core.py
The checker writes residue_core_verification.json beside itself and exits nonzero on failure.
It uses integer arithmetic, including exact // quotient and modular inverses.
The reported static audit counts floating-point literals and true-division syntax nodes; both are zero.

SCOPE
The written proofs establish their universal mathematical statements under the stated hypotheses. The finite checker verifies examples, boundary conditions, and explicit negative controls; it is not a universal proof by enumeration. It does not execute production CRAM APIs, rebuild Lean, or assess cryptographic security.
The displayed integers in tests are semantic oracles; they do not require runtime storage of scalar winding in the proposed architecture.
Figure geometry may use display-boundary floating point; mathematical counts and examples are exact integers.

EDITING
The separately supplied DOCX contains native editable Word mathematics. The PDF is the reviewed reading copy. The Markdown source references the relative figures/ directory, so keep that directory beside it when converting with a suitable Markdown tool.
The Greek appendix identifies Heiberg's edition reproduced by Fitzpatrick. It is not a diplomatic facsimile or a newly verified translation of the supplied English.

AUTHORSHIP AND STATUS
This is an AI-assisted research draft for the author to review. Established algebra, newly written derivations, inspected formal source, executed checks, and open application claims are distinguished in the manuscript. No independent priority determination is claimed.

PUBLICATION EDITORIAL REVISION — 15 November 2026
The manuscript opening and method follow the author’s clarified foundation: Euclid’s statements as written, their explicit consequences, and CRAM’s machine realization. Quoted appendices, theorem content, mathematical code and figures retain their original scope. Original packet hashes are retained under ../../evidence/historical/; SHA256SUMS.txt records this publication copy.

VERIFICATION REVIEW — 16 November 2026
The included universal Lean package was freshly checked: 130 theorem declarations, plus the standard package build and 1,809 executable comparison/divmod/GCD pairs with four controls. The Python reference checker again passed 821,881 assertions. The manuscript now points to the detailed formal-coverage map under ../../docs/reviews/. The fourteen written theorem sections have different coverage; their numbering is not a count of fully formalized results. Quoted appendices, theorem statements, proofs, figures, and mathematical source code are unchanged. The fresh evidence is under ../../evidence/current/.
