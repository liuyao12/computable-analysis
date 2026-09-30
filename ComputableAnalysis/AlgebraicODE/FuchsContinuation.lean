import ComputableAnalysis.Continuation.DifferentialEquation
import ComputableAnalysis.Continuation.Chain
import ComputableAnalysis.HolomorphicExamples
import ComputableAnalysis.AlgebraicODE.FuchsGrowth
import ComputableAnalysis.AlgebraicODE.FrobeniusConvergence

/-!
# An end-to-end Fuchs continuation client

The solution `y(z)=z²` of `z²y''-zy'=0` has actual represented complex
derivatives, holomorphic chart continuation along any supplied polygonal
route, and a compatible solution of the existing rational-ray growth API.
This is a polynomial mode of a regular-singular equation, not a construction
of general Frobenius branches or their monodromy.
-/
namespace ComputableAnalysis.AlgebraicODE.Fuchs.ContinuationExample
open ComplexRaw FunctionTheory Continuation LinearODE DiscreteLinearSystem

private def two : ComplexRaw := ofQComplex ⟨2,0⟩

private theorem twice_agrees (z : ComplexRaw) (hz : z.Valid) :
    (add z z).Equiv ((affine two zero (ofQComplex_valid _) (ofQComplex_valid _)).eval z) := by
  exact PolynomialExpr.identity (.add (.var 0) (.var 0))
    (.add (.mul (.lit ⟨2,0⟩) (.var 0)) (.lit ⟨0,0⟩))
    (fun _ => z) (fun _ => hz) (by
      intro p
      simp only [PolynomialExpr.rational,QComplex.add,QComplex.mul,QComplex.mk.injEq]
      constructor <;> grind)

private def derivativeModels : LocalModels square_holomorphic.derivativeMap where
  chart := fun _ => ⟨affine two zero (ofQComplex_valid _) (ofQComplex_valid _),
    affine_holomorphic two zero (ofQComplex_valid _) (ofQComplex_valid _)⟩
  radius := fun _ _ _ => ⟨1,by decide⟩
  agreement := fun _ _ _ z hz _ => ⟨True.intro,True.intro,twice_agrees z hz⟩

def derivative_holomorphic : Holomorphic square_holomorphic.derivativeMap :=
  derivativeModels.holomorphic

/-- The scaled Fuchs equation holds at every valid represented complex
input, including irrational inputs. There is no formal-derivative assumption. -/
theorem equation (z : ComplexRaw) (hz : z.Valid) :
    (secondOrderResidual square_holomorphic derivative_holomorphic z
      (mul z z) (neg z) zero).Equiv zero := by
  exact PolynomialExpr.identity
    (.add (.add (.mul (.mul (.var 0) (.var 0)) (.lit ⟨2,0⟩))
      (.mul (.neg (.var 0)) (.add (.var 0) (.var 0))))
      (.mul (.lit ⟨0,0⟩) (.mul (.var 0) (.var 0)))) (.lit ⟨0,0⟩)
    (fun _ => z) (fun _ => hz) (by
      intro p
      simp only [PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mul,QComplex.mk.injEq]
      constructor <;> grind)

def chart : Chart := ⟨square,square_holomorphic⟩

/-- A second evaluator for the same solution, expanded about `-1`.
Its interval boxes differ from direct squaring because of cancellation. -/
def recentered : FunctionTheory.Map where
  domain := fun _ => True
  eval := fun z => sub (mul (add z (ofQComplex ⟨1,0⟩)) (add z (ofQComplex ⟨1,0⟩)))
    (add (add z z) (ofQComplex ⟨1,0⟩))
  valid := fun z hz _ => sub_valid
    (mul_valid (add_valid hz (ofQComplex_valid _)) (add_valid hz (ofQComplex_valid _)))
    (add_valid (add_valid hz hz) (ofQComplex_valid _))
  domain_congr := fun _ _ _ => Iff.rfl
  eval_congr := by
    intro z w hz hw _ _ h
    have h1 := add_equiv h (equiv_refl _ (ofQComplex_valid ⟨1,0⟩))
    exact FunctionTheory.sub_congr
      (mul_equiv (add_valid hz (ofQComplex_valid _)) (add_valid hw (ofQComplex_valid _))
        (add_valid hz (ofQComplex_valid _)) (add_valid hw (ofQComplex_valid _)) h1 h1)
      (add_equiv (add_equiv h h) (equiv_refl _ (ofQComplex_valid _)))

theorem recentered_equiv (z : ComplexRaw) (hz : z.Valid) :
    (recentered.eval z).Equiv (square.eval z) := by
  let Z : PolynomialExpr := .var 0
  let U : PolynomialExpr := .lit ⟨1,0⟩
  exact PolynomialExpr.identity
    (.add (.mul (.add Z U) (.add Z U)) (.neg (.add (.add Z Z) U))) (.mul Z Z)
    (fun _ => z) (fun _ => hz) (by
      intro p
      simp only [Z,U,PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mul,QComplex.mk.injEq]
      constructor <;> grind)

theorem recentered_germ (a : Point) : AgreeAt a square recentered :=
  ⟨⟨1,by decide⟩,fun z hz _ => ⟨True.intro,True.intro,equiv_symm (recentered_equiv z hz)⟩⟩

def recentered_holomorphic : Holomorphic recentered where
  openDomain := { radius := fun _ _ _ => ⟨1,by decide⟩, inside := fun _ _ _ _ _ _ => True.intro }
  derivative := square_holomorphic.derivative
  derivative_congr := square_holomorphic.derivative_congr
  continuousDerivative := square_holomorphic.continuousDerivative
  atPoint := fun a ha _ => (square_holomorphic.atPoint a ha True.intro).congrMap
    ⟨1,by decide⟩ (fun z hz _ => ⟨True.intro,True.intro,equiv_symm (recentered_equiv z hz)⟩)

def recenteredChart : Chart := ⟨recentered,recentered_holomorphic⟩

/-- A genuine change of chart computation: direct squaring on the first
edge, a translated expression on the second, and a proved overlap. -/
def twoCharts {D : Region} {a b c : D.Vertex} (e : D.Edge a b) (d : D.Edge b c) :
    Along (.cons e (.cons d (.nil c)))
      (chart.at a.val True.intro) (recenteredChart.at c.val True.intro) :=
  .cons e chart True.intro True.intro (fun _ => True.intro) (Setoid.refl _)
    (.cons d recenteredChart True.intro True.intro (fun _ => True.intro)
      (recentered_germ b.val) (.nil (Setoid.refl _)))

/-- An actual chain with whole-segment coverage and neighborhood equality.
No simple-connectedness assumption is needed for this entire solution. -/
def along {D : Region} {a b : D.Vertex} (p : Path D.Edge a b) :
    Along p (chart.at a.val True.intro) (chart.at b.val True.intro) :=
  Along.singleChart chart p (fun _ => True.intro) (fun _ _ _ _ => True.intro)

/-- Any holomorphic terminal representative of this germ satisfies the
same second-order equation when its derivative is holomorphic. -/
theorem equation_of_germ {a : Point} {g : FunctionTheory.Map}
    (hg : Holomorphic g) (hdg : Holomorphic hg.derivativeMap)
    (h : AgreeAt a square g) :
    (secondOrderResidual hg hdg a.val (mul a.val a.val) (neg a.val) zero).Equiv zero := by
  obtain ⟨r,hr⟩ := h
  have hm := hr a.val a.property
    (Small.sub_self _ a.property (Rat.le_of_lt r.property))
  have hc := secondOrderResidual_congr square_holomorphic hg derivative_holomorphic hdg
    ⟨r,hr⟩ (mul a.val a.val) (neg a.val) zero
    (mul_valid a.property a.property) (neg_valid a.property) (ofQComplex_valid _)
  exact equiv_trans
    (secondOrderResidual_valid hg hdg a.property hm.2.1
      (mul_valid a.property a.property) (neg_valid a.property) (ofQComplex_valid _))
    (secondOrderResidual_valid square_holomorphic derivative_holomorphic a.property True.intro
      (mul_valid a.property a.property) (neg_valid a.property) (ofQComplex_valid _))
    (ofQComplex_valid _) (equiv_symm hc) (equation a.val a.property)

def recentered_derivative_holomorphic : Holomorphic recentered_holomorphic.derivativeMap := by
  change Holomorphic square_holomorphic.derivativeMap
  exact derivative_holomorphic

/-- The changed chart satisfies the ODE through derivative-germ comparison,
without independently differentiating its translated expression. -/
theorem recentered_equation (z : ComplexRaw) (hz : z.Valid) :
    (secondOrderResidual (f := recentered) recentered_holomorphic recentered_derivative_holomorphic z
      (mul z z) (neg z) zero).Equiv zero :=
  equation_of_germ (a := ⟨z,hz⟩) (g := recentered) recentered_holomorphic
    recentered_derivative_holomorphic (recentered_germ ⟨z,hz⟩)

def frobeniusEquation : Frobenius.Equation := ⟨[-1],[]⟩

/-- The existing Frobenius solver gives precisely the constant factor for
the exponent-two mode; this identifies all coefficients, not just a prefix. -/
theorem frobenius_coeff (n : Nat) :
    frobeniusEquation.coeff 2 1 n = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Frobenius.Equation.coeff_succ]
    have hl : frobeniusEquation.lower 2 (frobeniusEquation.coeff 2 1) (n+1) = 0 := by
      unfold Frobenius.Equation.lower
      have hs : ∀ N, FormalPowerSeries.sumBelow (fun _ => (0 : Rat)) N = 0 := by
        intro N; induction N with
        | zero => rfl
        | succ N ih => rw [FormalPowerSeries.sumBelow_succ,ih]; grind
      rw [← hs (n+1)]
      apply FormalPowerSeries.sumBelow_congr
      intro k hk
      have hpos : 0 < n+1-k := by omega
      obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      simp [frobeniusEquation, hj, FormalPowerSeries.ofPolynomial] <;> grind
    rw [hl]
    simp [Rat.div_def]

/-- Rational-ray values of the same scaled jet `(y,z y')`. -/
def rayJet (t : Rat) : RatVector 4 :=
  Growth.jetVector (QComplex.ofRat (t*t)) (QComplex.ofRat (2*(t*t)))

def rayRadius (_a _b : Rat) (eps : QPos) : QPos :=
  ⟨eps.val/3, by have := eps.property; grind⟩

theorem ray_residual {R : Rat} :
    ∀ a b (eps : QPos) x h,
      0 < a → a ≤ x → x ≤ b → a ≤ x+h → x+h ≤ b → b ≤ R →
      h ≠ 0 → qabs h ≤ (rayRadius a b eps).val →
      vectorAbsSum (fun i => rayJet (x+h) i-rayJet x i-
        h*matrixApply (Growth.rayMatrix [QComplex.ofRat (-1)] [] QComplex.one x)
          (rayJet x) i) ≤ eps.val*qabs h := by
  intro a b eps x h ha hax _ _ _ _ _ hd
  have hx : x ≠ 0 := by grind
  have hcancel := FormalPowerSeries.mul_div_cancel_left (a := x) (b := 1) hx
  have hid : (fun i => rayJet (x+h) i-rayJet x i-
      h*matrixApply (Growth.rayMatrix [QComplex.ofRat (-1)] [] QComplex.one x)
        (rayJet x) i) =
      (fun i : Fin 4 => if i.val = 0 then h*h else if i.val = 2 then 2*(h*h) else 0) := by
    funext i
    have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
      have := i.isLt; omega
    rcases hi with hi | hi | hi | hi <;>
      simp [rayJet,Growth.rayMatrix,Growth.companion,Growth.jetVector,matrixApply,
        matrixScale,finiteSum,CPoly.eval,QComplex.add,QComplex.mul,QComplex.zero,
        QComplex.ofRat,hi] <;> grind
  rw [hid]
  change qabs (h*h)+(qabs 0+(qabs (2*(h*h))+(qabs 0+0))) ≤ _
  simp only [qabs_mul,show qabs (0 : Rat) = 0 by decide,
    show qabs (2 : Rat) = 2 by decide]
  have hd' : 3*qabs h ≤ eps.val := by change qabs h ≤ eps.val/3 at hd; grind
  have := Rat.mul_le_mul_of_nonneg_right hd' (qabs_nonneg h)
  grind

def raySolution (R : Rat) : Growth.RaySolution [QComplex.ofRat (-1)] [] QComplex.one R :=
  LinearSolution.ofExact rayJet rayRadius ray_residual

private theorem square_compute (t : Rat) (n : Nat) :
    (square.eval (ofQComplex (QComplex.ofRat t))).compute n =
      QBox.point (QComplex.ofRat (t*t)) := by
  change QBox.mul (QBox.point _) (QBox.point _) = _
  rw [QBox.mul_point]
  congr 1
  simp [QComplex.mul,QComplex.ofRat] <;> grind

private theorem scaledDerivative_compute (t : Rat) (n : Nat) :
    (mul (ofQComplex (QComplex.ofRat t))
      (square_holomorphic.derivative (ofQComplex (QComplex.ofRat t)))).compute n =
      QBox.point (QComplex.ofRat (2*(t*t))) := by
  change QBox.mul (QBox.point _) (QBox.add (QBox.point _) (QBox.point _)) = _
  rw [QBox.add_point,QBox.mul_point]
  congr 1
  simp [QComplex.mul,QComplex.add,QComplex.ofRat] <;> grind

/-- Exact computational bridge: the ray solution's first two coordinates
are the real and imaginary parts of the continued holomorphic value. -/
theorem ray_value (R t : Rat) :
    ((raySolution R).value t 0).Equiv
      (square.eval (ofQComplex (QComplex.ofRat t))).realPart ∧
    ((raySolution R).value t 1).Equiv
      (square.eval (ofQComplex (QComplex.ofRat t))).imagPart := by
  constructor <;> intro n <;> apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  · change QInterval.Overlaps ⟨t*t,t*t⟩
      ⟨((square.eval (ofQComplex (QComplex.ofRat t))).compute n).lo.re,
       ((square.eval (ofQComplex (QComplex.ofRat t))).compute n).hi.re⟩
    rw [square_compute]
    exact ⟨Rat.le_refl,Rat.le_refl⟩
  · change QInterval.Overlaps ⟨0,0⟩
      ⟨((square.eval (ofQComplex (QComplex.ofRat t))).compute n).lo.im,
       ((square.eval (ofQComplex (QComplex.ofRat t))).compute n).hi.im⟩
    rw [square_compute]
    exact ⟨Rat.le_refl,Rat.le_refl⟩

/-- The other two coordinates are the scaled actual derivative `z y'`. -/
theorem ray_scaled_derivative (R t : Rat) :
    ((raySolution R).value t 2).Equiv
      (mul (ofQComplex (QComplex.ofRat t))
        (square_holomorphic.derivative (ofQComplex (QComplex.ofRat t)))).realPart ∧
    ((raySolution R).value t 3).Equiv
      (mul (ofQComplex (QComplex.ofRat t))
        (square_holomorphic.derivative (ofQComplex (QComplex.ofRat t)))).imagPart := by
  constructor <;> intro n <;> apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  · change QInterval.Overlaps ⟨2*(t*t),2*(t*t)⟩
      ⟨((mul (ofQComplex (QComplex.ofRat t))
        (square_holomorphic.derivative (ofQComplex (QComplex.ofRat t)))).compute n).lo.re,
       ((mul (ofQComplex (QComplex.ofRat t))
        (square_holomorphic.derivative (ofQComplex (QComplex.ofRat t)))).compute n).hi.re⟩
    rw [scaledDerivative_compute]
    exact ⟨Rat.le_refl,Rat.le_refl⟩
  · change QInterval.Overlaps ⟨0,0⟩
      ⟨((mul (ofQComplex (QComplex.ofRat t))
        (square_holomorphic.derivative (ofQComplex (QComplex.ofRat t)))).compute n).lo.im,
       ((mul (ofQComplex (QComplex.ofRat t))
        (square_holomorphic.derivative (ofQComplex (QComplex.ofRat t)))).compute n).hi.im⟩
    rw [scaledDerivative_compute]
    exact ⟨Rat.le_refl,Rat.le_refl⟩

theorem moderate {a : Rat} (ha : 0 < a) (ha1 : a ≤ 1) :
    NormBound ((raySolution 1).value a) (6/a^3) := by
  have hg := Growth.fuchs_ray_moderate [QComplex.ofRat (-1)] [] QComplex.one
    (raySolution 1) ha ha1 (Rat.le_refl (a := 1))
  have he : Growth.exponent [QComplex.ofRat (-1)] [] QComplex.one 1 = 3 := by decide +kernel
  have hn : normCeiling ((raySolution 1).value 1) 0 = 6 := by decide +kernel
  simpa [he,hn,Rat.pow_succ] using hg

end ComputableAnalysis.AlgebraicODE.Fuchs.ContinuationExample
