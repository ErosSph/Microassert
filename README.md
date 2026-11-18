# DAC2027

An evidence-linked research framework for RTL graph matching, local contracts,
cross-region SVA composition, and formal-feedback-driven refinement.


## Methods and Table of Contents

```text
RTL → Typed Semantic Graph → microarchitecture pattern matches → Regions
SPEC + Regions → local Contracts → deterministic SVA primitives → Local SVA
SPEC event ordering + contract interfaces → Composition IR → Composite SVA
JasperGold → proof/coverage evidence → incremental Region/Contract/composition feedback
```


## 1. Environment Setup

```bash
cd DATEAssertion2027
python3 -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -e '.[dev,audit]'
python -m pytest
dateassertion --help
```

## 2. Configure LLM

```bash
export LLM_BASE_URL='https://your-provider.example/v1'
export LLM_MODEL='your-enabled-model'
read -rs -p 'LLM API key: ' LLM_API_KEY; echo
export LLM_API_KEY
dateassertion check-llm --config configs/example.yaml
```
