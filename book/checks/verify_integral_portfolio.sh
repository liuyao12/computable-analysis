#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
export GITHUB_SHA="${SOURCE_SHA:-$(git rev-parse HEAD)}"
mkdir -p comparison/reports

echo "::group::Build native basepoint proofs and exponential companion"
lake build ComputableAnalysis.CosinePrimitive ComputableAnalysis.RotationSeries ComputableAnalysis.TrigonometricReadback
python3 blueprint/checks/check_two_cosine_proofs.py
python3 comparison/checks/check_boundary.py

echo "::endgroup::"

echo "::group::Resolve pinned comparison imports"
export MATHLIB_NO_CACHE_ON_UPDATE='1'
(cd comparison
lake update
git diff --exit-code -- lake-manifest.json
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = 51e6992efd06126df61a496bebf8f49482a4e129
lake exe cache get Mathlib.Analysis.SpecialFunctions.Integrals.Basic Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds Mathlib.Tactic

)
echo "::endgroup::"

echo "::group::Build all three proofs in one environment"
(cd comparison
lake build MathlibComparison MathlibComparison.ProofBenchExamples
)
echo "::endgroup::"

echo "::group::Check identical statement and independent proof routes"
(cd comparison
set -euo pipefail
mkdir -p reports
lake env lean checks/ThreeProofsAudit.lean | tee reports/three-proofs-audit.log
lake env lean checks/ExportBlueprintStatements.lean
lake env lean checks/ExportProofBench.lean | tee reports/proof-bench-audit.log

)
echo "::endgroup::"

echo "::group::Render blueprint and test the three-route graph"
leanblueprint web
python3 blueprint/checks/build_three_proof_graph.py
python3 blueprint/checks/enhance_blueprint_nodes.py
python3 blueprint/checks/add_proof_strategy.py
python3 blueprint/checks/audit_blueprint_definitions.py
python3 blueprint/checks/build_proof_bench.py
python3 blueprint/checks/test_proof_bench.py

echo "::endgroup::"

echo "::group::Test Lean statement boxes and Mathlib Real shading"
python -m pip install playwright
node blueprint/checks/test_lean_highlight.cjs
python3 blueprint/checks/test_statement_boxes.py
python3 blueprint/checks/test_proof_bench_browser.py
python3 blueprint/checks/test_definition_panels.py

echo "::endgroup::"

echo "::group::Audit the native computability boundary"
(cd comparison
set -euo pipefail
lake env lean checks/ComputabilityAudit.lean | tee reports/native-computability.log

)
echo "::endgroup::"

echo "::group::Build and verify the mathematical reader"
python3 book/checks/source_boundary.py
python3 book/build.py --commit "$GITHUB_SHA"
python3 book/checks/test_book.py
python3 book/checks/test_edge_semantics.py
python3 book/checks/browser.py
python3 book/checks/test_graph_roles_browser.py
python3 book/checks/test_geometric_panels.py
python3 book/checks/geometric_browser.py

echo "::endgroup::"

echo "::group::Verify the supplied-schedule lemmas and refined proof map"
set -euo pipefail
lake build ComputableAnalysis.IntegralSchedules
(cd comparison && lake env lean checks/ExportScheduleMap.lean) | tee comparison/reports/schedule-map.log
python3 book/refine_cosine_map.py
python3 book/checks/test_schedule_map.py
python3 book/checks/schedule_browser.py

echo "::endgroup::"

echo "::group::Verify the inline comparison and Mathlib foundations"
set -euo pipefail
(cd comparison && lake env lean checks/ExportMathlibMap.lean) | tee comparison/reports/mathlib-map.log
python3 book/expand_mathlib_map.py
python3 book/checks/test_mathlib_comparison.py
python3 book/checks/mathlib_comparison_browser.py

echo "::endgroup::"

echo "::group::Verify the radical evaluator and product theorem"
set -euo pipefail
lake build ComputableAnalysis.DyadicCosinePrimitive
lake env lean book/checks/ExportDyadicEvaluation.lean | tee comparison/reports/dyadic-evaluation.log
python3 book/add_dyadic_demo.py
python3 book/checks/test_dyadic_demo.py
python3 book/checks/dyadic_browser.py

echo "::endgroup::"

echo "::group::Check the arithmetic boundary and publish the planned application"
set -euo pipefail
lake build ComputableAnalysis.CartwrightArithmetic
lake env lean book/checks/ExportCartwrightArithmetic.lean | tee comparison/reports/cartwright-arithmetic.log
python3 book/add_cartwright_plan.py
python3 book/checks/test_cartwright_plan.py
python3 book/checks/cartwright_browser.py

echo "::endgroup::"

echo "::group::Complete cosine-moment proofs, audits and comparisons"
set -euo pipefail
lake build ComputableAnalysis.Cartwright
(cd comparison && lake build MathlibComparison.Cartwright && lake env lean checks/ExportCartwright.lean) | tee comparison/reports/cartwright-complete.log
python3 book/complete_cartwright.py
python3 book/checks/test_cartwright_complete.py
python3 book/checks/cartwright_complete_browser.py

echo "::endgroup::"

echo "::group::Verify paired Wallis and beta families"
lake build ComputableAnalysis.IntegralApplications
(cd comparison && lake build MathlibComparison.IntegralApplications)
(cd comparison && lake env lean checks/ExportIntegralPortfolio.lean) | tee comparison/reports/integral-portfolio.log
lake env lean book/checks/RunIntegralExamples.lean | tee comparison/reports/integral-native-examples.log
python3 book/add_integral_portfolio.py
python3 book/checks/test_integral_portfolio.py
python3 book/checks/integral_portfolio_browser.py
echo "::endgroup::"
python3 - <<'PYCHECK'
import json,os,pathlib
p=pathlib.Path('blueprint/web/reading')
manifest=json.loads((p/'manifest.json').read_text())
portfolio=json.loads((p/'integral-portfolio-audit.json').read_text())
assert manifest['sourceCommit']==os.environ['GITHUB_SHA']
assert all(portfolio['checks'].values())
print('VERIFIED SOURCE',manifest['sourceCommit'])
PYCHECK
