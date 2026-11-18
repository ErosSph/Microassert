# DATEAssertion2027

An evidence-linked research framework for RTL graph matching, local contracts,
cross-region SVA composition, and formal-feedback-driven refinement.


## 方法与目录

```text
RTL → Typed Semantic Graph → microarchitecture pattern matches → Regions
SPEC + Regions → local Contracts → deterministic SVA primitives → Local SVA
SPEC event ordering + contract interfaces → Composition IR → Composite SVA
JasperGold → proof/coverage evidence → incremental Region/Contract/composition feedback
```


## 1. 环境安装

推荐 Linux、Python 3.10 或更新版本。核心依赖：pyslang 11、NetworkX 3、PyYAML 6。

```bash
git clone git@github.com:ErosSph/DATEAssertion2027.git
cd DATEAssertion2027
python3 -m venv .venv
source .venv/bin/activate
python -m pip install --upgrade pip
python -m pip install -e '.[dev,audit]'
python -m pytest
dateassertion --help
```


## 2. 先跑完全离线示例

```bash
dateassertion doctor --config configs/example.yaml
dateassertion analyze --config configs/example.yaml --output outputs/controller_graph
```

## 3. 配置 LLM

```bash
export LLM_BASE_URL='https://your-provider.example/v1'
export LLM_MODEL='your-enabled-model'
read -rs -p 'LLM API key: ' LLM_API_KEY; echo
export LLM_API_KEY
dateassertion check-llm --config configs/example.yaml
```
