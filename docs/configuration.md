# Configuration reference

The CLI merges packaged `dateassertion/defaults.yaml` with the selected YAML file.
There is no dependency on a prior run, a notebook, or a workstation path.

| Section | Important fields |
|---|---|
| `design` | `design_id`, `top`, ordered `rtl_files`, `include_dirs`, `clock`, `reset`, `reset_active_low` |
| `design.spec` | `local_path`, `target_module`, `line_ranges`, provenance fields |
| `llm` | `provider`, `base_url`, `model`, `api_key_env`, `proxy`, `timeout_seconds`, `max_retries`, `max_tokens` |
| `formal` | `executable`, `license_env`, `license_file`, `prove_time_limit`, `coverage_time_limit`, `timeout_seconds` |
| `design_flow` | graph backend, candidate budgets, local selection, composition caps, SPEC context limits |
| `feedback` | round count, local/region/contract work budgets, composition context budgets, deduplication policy |

`LLM_BASE_URL` and `LLM_MODEL` override YAML. The key is read from the environment
variable named by `llm.api_key_env` (default `LLM_API_KEY`). `JASPERGOLD_BIN`
overrides the executable. `CDS_LIC_FILE` is inherited unless `license_file` is set.
Inline credential fields are rejected before writing resolved configuration.

Paths are resolved relative to the config file. Environment variables may appear
in paths; unresolved variables cause a clear error. The config only accepts
unescaped top/clock/reset identifiers. More complex clock/reset expressions need
an explicit extension rather than silent Tcl interpolation.

No universal ISA SPEC is supplied. When adding a design, select SPEC ranges
covering the intended verification scope and preserve source/revision evidence.
Optional downloads require an expected SHA-256 and a cache path.

`formal.prove_time_limit: 600s` limits the Jasper prove command, not the whole
pipeline. `coverage_time_limit` controls core measurement. `timeout_seconds`
is the wrapper deadline for one Jasper subprocess; 0 means no wrapper deadline.
The separate `measure` command retains its fixed final-measurement profile
documented in README; these values do not override that profile.

The desired composition fraction is a planning preference, not a fabricated
quota. No code is supposed to invent unsupported relations to reach a fraction.
`feedback.deduplicate_sva: false` preserves generated records. It does not turn
uninstantiated candidates or rejected malformed contracts into assertions.

Provider/network failures terminate the affected stage and retain evidence;
they are not treated as semantic rejections. Check `error.json`, stage artifacts,
and `formal/*/jaspergold.stdout.log`. Do not publish these files without review:
they can contain proprietary RTL/SPEC content or service metadata.
