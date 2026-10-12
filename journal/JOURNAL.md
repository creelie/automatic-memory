# Target journal: European Journal of Combinatorics

| Item | Details |
|---|---|
| Journal | European Journal of Combinatorics |
| Publisher | Elsevier |
| ISSN | 0195-6698 (print), 1095-9971 (electronic), confirmed in the Crossref journal record |
| Homepage | https://www.sciencedirect.com/journal/european-journal-of-combinatorics |
| Submission | "Submit your article" on the homepage, which opens the journal's Editorial Manager site, https://www.editorialmanager.com/ejc/ |
| Template | Elsevier `elsarticle` class (version 3.5, included as `paper/elsarticle.cls`), `preprint,12pt` option, numbered references with `elsarticle-num.bst` |

## Scope fit

The journal publishes research in all areas of combinatorics, including graph
invariants and their algebraic aspects. The two papers that settled the
neighbouring case c = 3/8 of the same question appeared there:

- D. Fomichev, M. Karev, The sl(2)-weight system at c = 3/8 for graphs,
  European J. Combin. 127 (2025) 104160, doi:10.1016/j.ejc.2025.104160.
- Q. Yan, Q. Deng, X. Jin, Proof of a conjecture of Fomichev and Karev,
  European J. Combin. 135 (2026) 104365, doi:10.1016/j.ejc.2026.104365.

The present paper settles the remaining value c = -3/32 named in
arXiv:2607.24217, with a combinatorial formula for the extension.

## Length and format

- The manuscript is 16 pages in the `elsarticle` preprint layout (12 pt, single
  column).
- Elsevier accepts a first submission as a single PDF; after acceptance the
  LaTeX source, the class file and the `.bib` or `.bbl` file are uploaded. The
  arXiv tarball in `dist/` contains exactly these files.
- Required front matter, all present: title, author with address and email,
  abstract, keywords, MSC 2020 codes (05C31, 57K16, 17B10).
- The journal's guide for authors page returned HTTP 403 to the session that
  prepared this file, so any journal-specific page limit or abstract length
  limit was not read; check the guide before submitting.
- Editorial Manager asks at submission for a declaration of competing
  interests and for funding information; these are filled in by the author on
  the submission form.

## Policy on AI assistance (Elsevier generative AI policy for journals)

- AI tools may not be listed as authors or cited as authors.
- Use of AI tools in manuscript preparation is disclosed in a separate section
  titled "Declaration of generative AI and AI-assisted technologies in the
  manuscript preparation process", placed before the references; the statement
  appears in the published article. Elsevier's recommended wording is used in
  `paper/main.tex`.
- Use of AI tools in the research process is described in the methods part of
  the paper; Section 7 (Formal verification) states it.
- The authors remain responsible for checking all AI-generated output,
  including references. Every reference in `paper/refs.bib` was checked against
  its Crossref record (DOI, volume, pages, year) or, for the arXiv preprint,
  against the arXiv source.
- Source: https://www.elsevier.com/about/policies-and-standards/generative-ai-policies-for-journals
