"""Apply recorded proof-only edits before checking the geometric development.
The workflow publishes them only after the entire target builds successfully.
"""
from pathlib import Path
root = Path(__file__).resolve().parents[2]
p = root/'ComputableAnalysis/GeometricSineSecant.lean'
s = p.read_text()
s = s.replace('  unfold QInterval.ContainsInterval at htan\n', '  unfold QInterval.ContainsInterval at htan\n  dsimp only at htan\n')
s = s.replace('  have habs : qabs (a-b-t) <= d*d+w := by\n',
              '  have hdd0 : 0 <= d*d := Rat.mul_nonneg hd0 hd0\n  have habs : qabs (a-b-t) <= d*d+w := by\n')
s = s.replace('    simp only [Rat.sub_self, qabs_zero, Rat.zero_mul, Rat.sub_zero, Rat.zero_add]\n',
              '    have habs0 : qabs (0 : Rat) = 0 := by decide +kernel\n'
              '    have hid : a-b-(u-u)*integralKernel u = a-b := by grind\n'
              '    dsimp only\n'
              '    rw [hid, Rat.sub_self, habs0]\n'
              '    simp only [Rat.mul_zero, Rat.zero_add]\n')
s = s.replace('      dsimp only at hs\n', '')
p.write_text(s)
p = root/'ComputableAnalysis/GeometricSineResidual.lean'
s = p.read_text().replace('    simp only [Rat.sub_self, Rat.zero_mul, Rat.sub_zero, qabs_zero,\n      Rat.mul_zero]\n    exact Rat.le_refl\n',
    '    have hz : qabs (0 : Rat) = 0 := by decide +kernel\n'
    '    simp only [Rat.sub_self, Rat.zero_mul, Rat.mul_zero, hz]\n'
    '    exact Rat.le_refl\n')
p.write_text(s)
