# Release validation

This document records packaging validation, not new CPU experiment results.

The migrated regression plus public CLI tests passed **121 tests** in a freshly
created Python 3.10 virtual environment (pytest 8.4.2). Tests cover typed graph
matching and negative fixtures, invariant generation, grounding, incremental
contract updates, LLM transport failure handling, and native coverage/Tcl parsing.
CLI, configuration, environment-only credentials, raw export and resume checks
are included. A mocked orchestration test exercises the full driver's file
layout and input-identity checks without claiming a real LLM/formal campaign.

Editable installation from scratch succeeded. Both the source distribution and
wheel built successfully, including prompts, ontology JSON, defaults and Tcl.
The wheel was also installed into an independent temporary directory and run
from outside the source tree: all 85 runtime modules imported successfully and
the Region-template smoke again generated 36 assertions. No research-workspace
imports or external source checkout was needed.

A real JasperGold 2021.12p002 smoke run of the original controller fixture with
the experimental Region-bound library produced 36 source assertions: 36 Proven,
0 CEX, 0 timeout, 0 not evaluated. Precondition diagnostics classified 10 as
vacuous and 26 as non-vacuous. This is an integration smoke test, **not evidence
of complete functional verification or a claim that all 36 are useful**.

The controller fixture is deliberately small. Release verification does not
rerun five full CPUs, ten feedback iterations, eight-hour mutation experiments,
or an external paid LLM campaign. Provider transport tests use controlled mock
responses; `check-llm` is available for an explicitly configured real service.

Native mutation exports and full measurement orchestration are regression-tested
with fixtures. Only the short proof/core smoke was actually launched for this
release; no native mutation percentage is invented.

Reproduce the offline checks with `python -m pytest`. Reproduce the structural
and Jasper smoke commands from README with a new output directory each time.
Raw test/Jasper artifacts are retained locally in ignored directories and are
not uploaded as if they were benchmark datasets.
