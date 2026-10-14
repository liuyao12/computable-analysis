import ComputableAnalysis.RiemannHilbert.ContourSystemUniqueness

/-! Names of actual holomorphic horizontal germs. Equality is agreement on
a positive neighborhood, independently of their values at the base point.
The ODE evaluation isomorphism is proved in `ConstructedSolutionGerms`. -/
namespace ComputableAnalysis.RiemannHilbert.AnalyticSolutionGerm
open ComplexRaw FunctionTheory LocalODE LocalSystem DomainFunctions LinearField
set_option autoImplicit false
variable {n : Nat} {D : Scalar → Prop}

structure Name (G : Field (n := n) (m := n) D) (b : Scalar) where
  function : DomainVectorFunctions.Map n
  holomorphic : DomainVectorFunctions.Holomorphic function
  base_mem : function.domain b
  contained : ∀ z, function.domain z → D z
  horizontal : ∀ z hz, DomainVectorFunctions.derivative function holomorphic z hz≈
    (G z (contained z hz)).eval (function.eval z hz)

variable {G : Field (n := n) (m := n) D} {b : Scalar}

def neighborhood (x : Name G b) : QPos := x.holomorphic.openDomain.radius b x.base_mem

theorem neighborhood_inside (x : Name G b) (z : Scalar)
    (hz : Centered.domain b (neighborhood x).val z) : x.function.domain z :=
  x.holomorphic.openDomain.inside b x.base_mem z (interior_bound (neighborhood x).val (Centered.offset b z) hz)

/-- Actual agreement on a common positive neighborhood, including both
domain inclusions. It does not refer to initial-value equality. -/
def Agreement (x y : Name G b) : Prop :=
  ∃ R : QPos,
    (∀ z, Centered.domain b R.val z → x.function.domain z) ∧
    (∀ z, Centered.domain b R.val z → y.function.domain z) ∧
    ∀ z, Centered.domain b R.val z → ∀ hx hy, x.function.eval z hx≈y.function.eval z hy

theorem agreement_refl (x : Name G b) : Agreement x x :=
  ⟨neighborhood x, neighborhood_inside x, neighborhood_inside x, fun _ _ _ _ => Setoid.refl _⟩

theorem agreement_symm {x y : Name G b} (h : Agreement x y) : Agreement y x := by
  obtain ⟨R,hx,hy,he⟩ := h
  exact ⟨R,hy,hx,fun z hz a c => Setoid.symm (he z hz c a)⟩

theorem agreement_trans {x y z : Name G b} (hxy : Agreement x y) (hyz : Agreement y z) : Agreement x z := by
  obtain ⟨R,hx,hy,he⟩ := hxy
  obtain ⟨S,hy',hz,hf⟩ := hyz
  let T := minRadius R S
  have hR : ∀ w, Centered.domain b T.val w → Centered.domain b R.val w :=
    fun w hw => interior_mono _ _ (Centered.offset b w) (minRadius_left R S) hw
  have hS : ∀ w, Centered.domain b T.val w → Centered.domain b S.val w :=
    fun w hw => interior_mono _ _ (Centered.offset b w) (minRadius_right R S) hw
  exact ⟨T,fun w hw => hx w (hR w hw),fun w hw => hz w (hS w hw),
    fun w hw a c => Setoid.trans (he w (hR w hw) a (hy w (hR w hw)))
      (hf w (hS w hw) (hy w (hR w hw)) c)⟩

instance nameSetoid : Setoid (Name G b) where
  r := Agreement
  iseqv := ⟨agreement_refl,agreement_symm,agreement_trans⟩

def evaluation : ValueMap (Name G b) (Fiber n) where
  eval x := x.function.eval b x.base_mem
  congr h := by
    obtain ⟨R,_,_,he⟩ := h
    exact he b (Centered.center_mem b R) _ _

theorem evaluation_congr {x y : Name G b} (h : x≈y) : evaluation.eval x≈evaluation.eval y :=
  evaluation.congr h

/-- Changing a representative of the same base point keeps the actual
function and its holomorphy and horizontality evidence. -/
def relabel (c : Scalar) (hbc : b≈c) (x : Name G b) : Name G c where
  function := x.function
  holomorphic := x.holomorphic
  base_mem := (x.function.domain_congr b c hbc).1 x.base_mem
  contained := x.contained
  horizontal := x.horizontal

theorem relabel_evaluation (c : Scalar) (hbc : b≈c) (x : Name G b) :
    evaluation.eval (relabel c hbc x)≈evaluation.eval x :=
  x.function.eval_congr c b _ _ (Setoid.symm hbc)

theorem relabel_congr (c : Scalar) (hbc : b≈c) {x y : Name G b} (h : x≈y) :
    relabel c hbc x≈relabel c hbc y := by
  obtain ⟨R,hx,hy,he⟩ := h
  have hi : ∀ z, Centered.domain c R.val z → Centered.domain b R.val z :=
    fun z hz => (Centered.domain_congr b c z z R.val hbc (Setoid.refl z)).2 hz
  exact ⟨R,fun z hz => hx z (hi z hz),fun z hz => hy z (hi z hz),
    fun z hz a d => he z (hi z hz) a d⟩

def relabelMap (c : Scalar) (hbc : b≈c) : ValueMap (Name G b) (Name G c) :=
  ⟨relabel c hbc,relabel_congr c hbc⟩

def relabelIso (c : Scalar) (hbc : b≈c) : ValueIso (Name G b) (Name G c) where
  forward := relabelMap c hbc
  backward := relabelMap b (Setoid.symm hbc)
  backward_forward x := agreement_refl x
  forward_backward x := agreement_refl x

end ComputableAnalysis.RiemannHilbert.AnalyticSolutionGerm
