# Journal submission details

Paper: The sl(2) weight system at c = -3/32 extends to a graph 4-invariant
Selected journal: **European Journal of Combinatorics**.
Recommended article type: original research article (editorial classification may differ).
Scope assessment: The explicit graph invariant and its links with Lie algebra weight systems fit the journal's combinatorial and algebraic scope. The neighbouring c=3/8 specialization was treated in this journal.

The selection is based on subject fit and the present contribution. It is not
a guarantee of editorial suitability or acceptance. The manuscript uses the Elsevier elsarticle preprint layout, with one article and inline references.
No journal submission has been performed by preparing these files.

Official scope: https://shop.elsevier.com/journals/european-journal-of-combinatorics/0195-6698
Author guide: https://www.sciencedirect.com/journal/european-journal-of-combinatorics/publish/guide-for-authors
Submission entry point: https://www.sciencedirect.com/journal/european-journal-of-combinatorics
Requirements checked on: 25 October 2026.
Access note: The journal-specific guide returned HTTP 403 to automated retrieval. The publisher scope page and current general Elsevier AI policy were accessible. Recheck the live guide and portal before submission; no assertion is made that an unread journal-specific requirement was satisfied.

## Upload files

- Manuscript PDF: Sl2_weight_system_at_minus_3_over_32_graph_4_invariant.pdf
- Editable manuscript source: Sl2_weight_system_at_minus_3_over_32_graph_4_invarianttex.zip; main document main.tex, pdfLaTeX.
- Cover letter PDF: coverletterjournal.pdf; editable source: coverlettertex.zip.
- AI disclosure: journalaideclarationform.pdf, an author-prepared declaration,
  not an official signed publisher form; its editable TeX is included separately.
- Provenance: AI_PROVENANCE.md / aiprovinance.md (identical content).
- Verification and data: https://github.com/creelie/automatic-memory .

## Disclosure and scope

The paper proves Conjecture 4.1 of Fomichev, Karev, Pavutnitskiy and Usanov: the sl(2) weight system at c=-3/32 extends to a graph four-invariant. The explicit signed-count construction works on every finite graph and agrees with the matrix-defined weight system on every chord diagram. This revision adds a normal-form proof and clarifies verification scope.

Formal-check scope: The universal extension theorem and its matrix-trace definition are formalized in Lean 4.34.1 with pinned Mathlib. At the unchanged proof-source commit, the complete build and four endpoint axiom reports passed with only propext, Classical.choice and Quot.sound. Python exact checks were rerun locally; Julia, C and C++ passed in the archived full run. The grouping proof for part (a) and the added faithful-action lemma are supplied in the written argument; no new formalization of the abstract Weyl algebra is claimed.

Existing preprint: https://hexagonmath.org/2610.00320v1
Existing manuscript/source DOI: https://doi.org/10.5281/zenodo.23541142
No arXiv identifier is supplied or invented. No journal acceptance or existing
journal publication is asserted. The new package archive DOI is recorded in
release-verification.json after Zenodo actually publishes it.

## AI disclosure

Claude (Anthropic) assisted the original mathematical exploration, proof, text, figures, Lean development and checking code. OpenAI Codex assisted this revision's proof and definition audit, elementary faithful-action argument, literature checks, verification records and submission files. These uses include research and writing assistance. The human authors retain responsibility for the final mathematics and submission decisions.

The author has stated that all parts are checked and understood by a human.
This is recorded as the user's declaration, not a substitute for the journal's
editorial review. The standalone disclosure is provided in addition to the
manuscript's existing AI section; it does not replace any declaration required
within the article. For Elsevier journals, the general policy asks for a
tool-and-purpose declaration in the manuscript before the references, and
separate research-method disclosure where AI is used in research.

Official general AI policy (Elsevier journals): https://www.elsevier.com/about/policies-and-standards/generative-ai-policies-for-journals
AMS publication entry point (Paper 5): https://www.ams.org/publications

Before submission, the author confirms coauthor approval where applicable,
current correspondence details, funding/competing interests, figure rights,
and the journal's current declarations in the live portal. The cover letter
does not certify exclusivity, financial disclosures, reviewer suggestions or
signatures that the author has not supplied. Submit to one journal at a time.
