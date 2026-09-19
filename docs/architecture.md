# Architecture and evidence boundaries

The packaged production flow is the existing graph/contract/feedback method,
not the unrelated transaction cold-start project and not an LLM-only baseline.

1. `rtl_frontend/parser.py` extracts modules, signals, assignments, guards,
   widths, source locations and clock/reset information using pyslang.
2. `semantic_graph.py` builds typed DATA/CONTROL/SEQUENTIAL dependencies.
   `graph_motif_matching.py` uses attributed graph matching and additional
   semantic predicates. `graph_motif_library.py` contains the matching knowledge.
3. `pipeline/semantic_slicing.py` expands matched cores into potentially
   overlapping verification Regions. A structural candidate is not an ISA claim.
4. `spec_extraction.py`, `local_region_assertions.py` and the contract grounding
   modules map SPEC intent and RTL evidence to local obligations. `ontology/primitives.py`
   compiles supported role bindings into SVA; malformed/unsupported bindings are recorded.
5. `local_contract_composition.py` and `composition_expansion.py` build candidate
   event relations from SPEC interpretation, contract interfaces, chain consistency
   and available evidence. The search is bounded, not exhaustive or complete.
6. `feedback_loop.py` uses measured gaps and updates incident contract relations
   incrementally. Candidate probes and the strict active portfolio are distinct
   from the full, unfiltered generated assertion export.
7. `formal/` and `coverage_analysis/` preserve tool results, target-level evidence,
   per-item coverage status, effective denominators, and counterexample references.

## Libraries

The current graph library contains 19 structure categories and 25 motifs.
The primitive compiler contains 19 fixed primitives. Legacy local relations
and template construction sites are not additional independent primitives.
Inspect `rtl_frontend/graph_motif_library.py` for exact edges and predicates,
and `ontology/primitives.py` for exact schemas and SVA bodies.

The experimental Region-bound library has FSM (5 recipes), DECODE (3),
REGISTER_UPDATE (3), PIPELINE (3), ONEHOT_PROGRESS (2): 16 recipes reusing
8 primitives. `experimental/region_templates.py` includes applicability
conditions and symbolic forms. `experimental/region_binding.py` instantiates
them from literal matched roles and complete producer families. One recipe can
yield multiple properties; some recipes yield none. This is opt-in and has
not replaced the production planner. Its known width/hold limitations remain.

## Packaging decisions

- Runtime code is namespaced under `dateassertion`, avoiding the previous
  top-level `coverage` collision with Python's coverage package.
- Orchestration modules are named by responsibility rather than experiment IDs.
- Prompts, ontology JSON and native Tcl reporters are included in the wheel.
- Only the import closure and reusable core support were migrated. Historical
  benchmark runners, plot scripts, web admin tools and private datasets were not.
- Existing raw statuses and scientific semantics were retained. A few internal
  historical schema/comment labels may remain; they are not public entrypoints.
- `migration_manifest.json` records source/export hashes at extraction time.
  Subsequent portability fixes are recorded in the release Git history; that
  manifest is provenance, not a final-file integrity lock.

No claim is made that an RTL-derived property independently validates the SPEC,
that CEX implies a DUT bug, that timeout implies correctness, or that proof-core
membership grows monotonically when adding assertions.
