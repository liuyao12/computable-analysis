import ComputableAnalysis.RiemannHilbert.ContourSystemODE
import ComputableAnalysis.RiemannHilbert.ContourVectorUniform

/-! Local uniqueness against an independently supplied holomorphic solution.
The common radius, bounds and uniform derivative errors are constructed;
callers supply only actual holomorphy, the function ODE and initial equality. -/
namespace ComputableAnalysis.RiemannHilbert.ConstructedSystemODE
open ComplexRaw FunctionTheory LocalSystem DomainFunctions LinearField
set_option autoImplicit false
variable {n : Nat} {D : Scalar → Prop}
variable (G : Field (n := n) (m := n) D) (O : ScalarTopology.OpenData D)
    (hG : ∀ z w hz hw, z≈w → (G z hz).Equiv (G w hw))
    (hM : MatrixHolomorphic G O.invariant hG) (b : Scalar) (hb : D b)
    (g : DomainVectorFunctions.Map n) (hg : DomainVectorFunctions.Holomorphic g) (hgb : g.domain b)

def comparisonRadius : QPos := minRadius (radius G O hG hM b hb) (ConstructedVectorTaylor.radius g hg b hgb)

theorem comparison_system (z : Scalar) (hz : Centered.domain b (comparisonRadius G O hG hM b hb g hg hgb).val z) :
    domain G O hG hM b hb z := interior_mono _ _ (Centered.offset b z) (minRadius_left _ _) hz

theorem comparison_vector (z : Scalar) (hz : Centered.domain b (comparisonRadius G O hG hM b hb g hg hgb).val z) :
    Centered.domain b (ConstructedVectorTaylor.radius g hg b hgb).val z := interior_mono _ _ (Centered.offset b z) (minRadius_right _ _) hz

theorem comparison_original (z : Scalar) (hz : Centered.domain b (comparisonRadius G O hG hM b hb g hg hgb).val z) :
    g.domain z := ConstructedVectorTaylor.domain_original g hg b hgb z (comparison_vector G O hG hM b hb g hg hgb z hz)

theorem comparison_small : 2*(comparisonRadius G O hG hM b hb g hg hgb).val*(8*(chart G O hG hM b hb).M)≤(1:Rat)/2 := by
  let c := chart G O hG hM b hb
  have hr : (comparisonRadius G O hG hM b hb g hg hgb).val≤c.radius.val :=
    Rat.le_trans (minRadius_left _ _) (ConstructedMatrixTaylor.radius_ode_le G O hG hM b hb)
  have hs := LocalODE.solutionRadius_small c.K c.nonnegK
  have hMR := Rat.mul_le_mul_of_nonneg_right c.compatible (Rat.le_of_lt (comparisonRadius G O hG hM b hb g hg hgb).property)
  have hKR := Rat.mul_le_mul_of_nonneg_left hr c.nonnegK
  change 8*c.K*c.radius.val≤(1:Rat)/2 at hs
  grind only

/-- Any actual holomorphic solution with the same initial value agrees with
the constructed solution on a computed positive common neighborhood. -/
theorem solution_unique_local (hlinear : ∀ z hz, IsLinear (G z hz)) (initial : Fiber n)
    (hinit : g.eval b hgb≈initial)
    (hODE : ∀ z hz ha, DomainVectorFunctions.derivative g hg z hz≈(G z ha).eval (g.eval z hz))
    (z : Scalar) (hz : Centered.domain b (comparisonRadius G O hG hM b hb g hg hgb).val z) :
    (solution G O hG hM b hb initial).eval z (comparison_system G O hG hM b hb g hg hgb z hz)≈
      g.eval z (comparison_original G O hG hM b hb g hg hgb z hz) := by
  let c := chart G O hG hM b hb
  let R := comparisonRadius G O hG hM b hb g hg hgb
  let hs := comparison_system G O hG hM b hb g hg hgb
  let hv := comparison_vector G O hG hM b hb g hg hgb
  let ho := comparison_original G O hG hM b hb g hg hgb
  let hc := fun z hz => domain_chart G O hG hM b hb z (hs z hz)
  let ha := fun z hz => domain_original G O hG hM b hb z (hs z hz)
  let A : Centered.OperatorField (n := n) b R.val := fun z hz => c.operator z (hc z hz)
  let f : Centered.Field (n := n) b R.val := fun z hz => c.value initial z (hc z hz)
  let u : Centered.Field (n := n) b R.val := fun z hz => g.eval z (ho z hz)
  refine Centered.equal b R A f u (8*c.M) (4*initialBound initial) (4*ConstructedVectorTaylor.bound g hg b hgb)
    (Rat.mul_nonneg (by decide +kernel) c.nonnegM) (comparison_small G O hG hM b hb g hg hgb)
    (Rat.mul_nonneg (by decide +kernel) (initialBound_nonneg initial))
    (Rat.mul_nonneg (by decide +kernel) (ConstructedVectorTaylor.bound_nonneg g hg b hgb))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ (c.delta initial) (ConstructedVectorTaylor.delta g hg b hgb) ?_ ?_ z hz
  · intro z w hz hw he
    exact c.value_congr c initial initial (equiv_refl _ b.property) (fun _ => ValueMap.equiv_refl _)
      (Setoid.refl _) z w he (hc z hz) (hc w hw)
  · intro z w hz hw he
    exact g.eval_congr z w (ho z hz) (ho w hw) he
  · exact Setoid.trans (c.value_initial initial) (Setoid.symm hinit)
  · intro z hz
    exact c.value_bound initial z (hc z hz)
  · intro z hz
    exact ConstructedVectorTaylor.value_bound g hg b hgb z (hv z hz) (ho z hz)
  · intro z hz
    exact c.operator_linear z (hc z hz)
  · intro z hz E hE x hx
    exact c.operator_bound z (hc z hz) E hE x hx
  · intro eps H w z hw hz hH hzw
    exact c.value_uniform_remainder initial eps H w z (hc w hw) (hc z hz) hH hzw
  · intro eps H w z hw hz hH hzw
    have hr := ConstructedVectorTaylor.uniform_remainder g hg b hgb eps H w z (hv w hw) (hv z hz)
      (ho w hw) (ho z hz) hH hzw
    have hd : DomainVectorFunctions.derivative g hg w (ho w hw)≈(A w hw).eval (u w hw) :=
      Setoid.trans (hODE w (ho w hw) (ha w hw))
        (Setoid.symm (operator_agrees G O hG hM b hb hlinear w (hs w hw) (ha w hw) (g.eval w (ho w hw))))
    exact bound_congr (Fiber.sub_congr (Setoid.refl _) (Fiber.scale_congr
      (a := (⟨sub z.val w.val,sub_valid z.property w.property⟩ : Scalar)) (equiv_refl _ (sub_valid z.property w.property)) hd)) hr

end ComputableAnalysis.RiemannHilbert.ConstructedSystemODE
