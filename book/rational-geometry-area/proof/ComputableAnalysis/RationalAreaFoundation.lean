import Init.Grind.Ordered.Rat

/-! Finite rational area model for the geometry-foundation proposal.
No distance, square-root, completed-real, integral, or trig function is imported.
`squareContent` is the oriented content of the square erected by `quarter`.
The polygon-dissection interpretation and the curved-region area specification
are discussed separately in docs/RATIONAL_GEOMETRY_AREA_FOUNDATION.md. -/
namespace ComputableAnalysis.RationalAreaFoundation
set_option maxHeartbeats 1000000

structure Point where
  x : Rat
  y : Rat
  deriving DecidableEq, Repr

def add (u v : Point) : Point := ⟨u.x+v.x,u.y+v.y⟩
def scale (k : Rat) (u : Point) : Point := ⟨k*u.x,k*u.y⟩
def quarter (u : Point) : Point := ⟨-u.y,u.x⟩
def content (u v : Point) : Rat := u.x*v.y-u.y*v.x
def squareContent (u : Point) : Rat := content u (quarter u)

private theorem square_nonnegative (x : Rat) : 0 ≤ x*x := by
  by_cases hx : 0 ≤ x
  · exact Rat.mul_nonneg hx hx
  · have hn : 0 ≤ -x := by grind
    have h := Rat.mul_nonneg hn hn
    grind

private theorem product_ge_one {a b : Rat} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ a*b := by
  have ha0 : 0 ≤ a := by grind
  have h := Rat.mul_le_mul_of_nonneg_left hb ha0
  grind

theorem content_add_left (u v w : Point) :
    content (add u v) w = content u w+content v w := by
  unfold content add
  grind

theorem content_skew (u v : Point) : content u v = -content v u := by
  unfold content
  grind

theorem quarter_twice (u : Point) : quarter (quarter u) = scale (-1) u := by
  cases u
  simp [quarter,scale]
  constructor <;> grind

theorem quarter_preserves_content (u v : Point) :
    content (quarter u) (quarter v) = content u v := by
  unfold content quarter
  grind

theorem quarter_add (u v : Point) :
    quarter (add u v)=add (quarter u) (quarter v) := by
  cases u
  cases v
  simp [quarter,add]
  grind

theorem quarter_scale (k : Rat) (u : Point) :
    quarter (scale k u)=scale k (quarter u) := by
  cases u
  simp [quarter,scale]
  grind

/-- Abstract square-area Pythagoras from the finite algebra of oriented
parallelogram areas. No coordinate formula for the supplied area B is assumed.
Deriving these area laws from polygon dissection is a separate bridge. -/
theorem area_pythagoras_of_bilinear
    (B : Point → Point → Rat)
    (add_left : ∀ u v w, B (add u v) w=B u w+B v w)
    (add_right : ∀ u v w, B u (add v w)=B u v+B u w)
    (scale_left : ∀ k u v, B (scale k u) v=k*B u v)
    (scale_right : ∀ k u v, B u (scale k v)=k*B u v)
    (alternating : ∀ u, B u u=0)
    (u : Point) (k : Rat) :
    B (add u (scale k (quarter u))) (quarter (add u (scale k (quarter u))))=
      B u (quarter u)+B (scale k (quarter u)) (quarter (scale k (quarter u))) := by
  rw [quarter_add,add_left,add_right,add_right]
  have hc1 : B u (quarter (scale k (quarter u)))=0 := by
    rw [quarter_scale,quarter_twice,scale_right,scale_right,alternating]
    grind
  have hc2 : B (scale k (quarter u)) (quarter u)=0 := by
    rw [scale_left,alternating]
    grind
  rw [hc1,hc2]
  grind

theorem square_content_coordinates (u : Point) :
    squareContent u = u.x*u.x+u.y*u.y := by
  unfold squareContent content quarter
  grind

theorem square_content_nonnegative (u : Point) : 0 ≤ squareContent u := by
  rw [square_content_coordinates]
  have hx : 0 ≤ u.x*u.x := square_nonnegative _
  have hy : 0 ≤ u.y*u.y := square_nonnegative _
  grind

/-- Pythagoras stated in areas of squares; the right-angle condition says
the second side is a rational multiple of a quarter-turn of the first. -/
theorem pythagoras_square_areas (u : Point) (k : Rat) :
    squareContent (add u (scale k (quarter u))) =
      squareContent u+squareContent (scale k (quarter u)) := by
  simp only [square_content_coordinates,add,scale,quarter]
  grind

/-- Algebraic certificate for the standard four-triangle dissection.
Coverage of the displayed polygons is a separate geometric proof obligation. -/
theorem four_triangle_dissection_content (a b : Rat) :
    (a+b)*(a+b) = squareContent ⟨b,a⟩+4*(a*b/2) := by
  rw [square_content_coordinates]
  change _ = b*b+a*a+4*(a*b/2)
  grind

def similarity (a b : Rat) (u : Point) : Point :=
  ⟨a*u.x-b*u.y,b*u.x+a*u.y⟩

theorem similarity_content (a b : Rat) (u v : Point) :
    content (similarity a b u) (similarity a b v) =
      (a*a+b*b)*content u v := by
  unfold content similarity
  grind

theorem similarity_square_content (a b : Rat) (u : Point) :
    squareContent (similarity a b u) = (a*a+b*b)*squareContent u := by
  simp only [square_content_coordinates,similarity]
  grind

/-- A single-circle chart. Its parameter is a rational slope coordinate,
not an angle and not a definition of sine or cosine. -/
def circlePoint (u : Rat) : Point :=
  ⟨(1-u*u)/(1+u*u),2*u/(1+u*u)⟩

private theorem denominator_pos (u : Rat) : 0 < 1+u*u := by
  have h := square_nonnegative u
  grind

private theorem chart_coordinates (u : Rat) :
    (circlePoint u).x*(1+u*u)=1-u*u ∧
      (circlePoint u).y*(1+u*u)=2*u := by
  unfold circlePoint
  exact ⟨Rat.div_mul_cancel (Rat.ne_of_gt (denominator_pos u)),
    Rat.div_mul_cancel (Rat.ne_of_gt (denominator_pos u))⟩

theorem circle_point_square_content (u : Rat) :
    squareContent (circlePoint u) = 1 := by
  have h := chart_coordinates u
  have hp := denominator_pos u
  rw [square_content_coordinates]
  grind

def innerWedge (u v : Rat) : Rat :=
  (v-u)*(1+u*v)/((1+u*u)*(1+v*v))

def outerWedge (u v : Rat) : Rat := (v-u)/(1+u*v)

theorem inner_wedge_triangle_content (u v : Rat) :
    innerWedge u v = content (circlePoint u) (circlePoint v)/2 := by
  have hu := chart_coordinates u
  have hv := chart_coordinates v
  have hpu := denominator_pos u
  have hpv := denominator_pos v
  have hden := Rat.mul_pos hpu hpv
  have hcancel := Rat.div_mul_cancel
    (a := (v-u)*(1+u*v)) (Rat.ne_of_gt hden)
  unfold innerWedge content
  grind

def tangentIntersection (u v : Rat) : Point :=
  ⟨(1-u*v)/(1+u*v),(u+v)/(1+u*v)⟩

def pairing (u v : Point) : Rat := content u (quarter v)

theorem tangent_intersection_supporting_lines {u v : Rat}
    (hu : 0 ≤ u) (hv : u ≤ v) :
    pairing (circlePoint u) (tangentIntersection u v)=1 ∧
      pairing (circlePoint v) (tangentIntersection u v)=1 := by
  have hv0 := Rat.le_trans hu hv
  have huv := Rat.mul_nonneg hu hv0
  have hp : 0 < 1+u*v := by grind
  have ht1 := Rat.div_mul_cancel (a:=1-u*v) (Rat.ne_of_gt hp)
  have ht2 := Rat.div_mul_cancel (a:=u+v) (Rat.ne_of_gt hp)
  have hcu := chart_coordinates u
  have hcv := chart_coordinates v
  have hpu := denominator_pos u
  have hpv := denominator_pos v
  unfold pairing content quarter tangentIntersection
  constructor <;> grind

theorem outer_wedge_quadrilateral_content {u v : Rat}
    (hu : 0 ≤ u) (hv : u ≤ v) :
    outerWedge u v =
      (content (circlePoint u) (tangentIntersection u v)+
        content (tangentIntersection u v) (circlePoint v))/2 := by
  have hv0 := Rat.le_trans hu hv
  have huv := Rat.mul_nonneg hu hv0
  have hp : 0 < 1+u*v := by grind
  have ht1 := Rat.div_mul_cancel (a:=1-u*v) (Rat.ne_of_gt hp)
  have ht2 := Rat.div_mul_cancel (a:=u+v) (Rat.ne_of_gt hp)
  have ho := Rat.div_mul_cancel (a:=v-u) (Rat.ne_of_gt hp)
  have hcu := chart_coordinates u
  have hcv := chart_coordinates v
  have hpu := denominator_pos u
  have hpv := denominator_pos v
  unfold outerWedge content tangentIntersection
  grind

theorem unit_disk_support {p z : Point} (hp : squareContent p=1)
    (hz : squareContent z ≤ 1) : pairing p z ≤ 1 := by
  have h := square_content_nonnegative (add z (scale (-1) p))
  simp only [square_content_coordinates] at hp hz h
  unfold add scale at h
  unfold pairing content quarter
  grind

/-- Exact finite polygon gap. On the unit chart all three denominators
are at least one, so the cubic error bound below needs only rational order. -/
theorem wedge_gap_identity {u v : Rat} (hu : 0 ≤ u) (hv : u ≤ v) :
    outerWedge u v-innerWedge u v =
      (v-u)*(v-u)*(v-u)/((1+u*v)*(1+u*u)*(1+v*v)) := by
  have hv0 : 0 ≤ v := Rat.le_trans hu hv
  have huv : 0 ≤ u*v := Rat.mul_nonneg hu hv0
  have h0 : 0 < 1+u*v := by grind
  have h1 := denominator_pos u
  have h2 := denominator_pos v
  have hp12 := Rat.mul_pos h1 h2
  have hp012 := Rat.mul_pos (Rat.mul_pos h0 h1) h2
  have ho := Rat.div_mul_cancel (a:=v-u) (Rat.ne_of_gt h0)
  have hi := Rat.div_mul_cancel (a:=(v-u)*(1+u*v)) (Rat.ne_of_gt hp12)
  have hg := Rat.div_mul_cancel (a:=(v-u)*(v-u)*(v-u)) (Rat.ne_of_gt hp012)
  unfold innerWedge outerWedge
  grind

theorem wedge_gap_bounds {u v : Rat} (hu : 0 ≤ u) (hv : u ≤ v) :
    0 ≤ outerWedge u v-innerWedge u v ∧
      outerWedge u v-innerWedge u v ≤ (v-u)*(v-u)*(v-u) := by
  rw [wedge_gap_identity hu hv]
  have hv0 : 0 ≤ v := Rat.le_trans hu hv
  have huv := Rat.mul_nonneg hu hv0
  have huu := square_nonnegative u
  have hvv := square_nonnegative v
  have h01 : 1 ≤ (1+u*v)*(1+u*u) := product_ge_one (by grind) (by grind)
  have hden : 1 ≤ (1+u*v)*(1+u*u)*(1+v*v) := product_ge_one h01 (by grind)
  have hdpos : 0 < (1+u*v)*(1+u*u)*(1+v*v) := by grind
  have hdiff : 0 ≤ v-u := by grind
  have hc := Rat.mul_nonneg (Rat.mul_nonneg hdiff hdiff) hdiff
  have hcancel := Rat.div_mul_cancel
    (a:=(v-u)*(v-u)*(v-u)) (Rat.ne_of_gt hdpos)
  constructor
  · have hinv := Rat.le_of_lt (Rat.inv_pos.mpr hdpos)
    exact Rat.mul_nonneg hc hinv
  · apply Rat.le_of_mul_le_mul_right (c:=(1+u*v)*(1+u*u)*(1+v*v)) _ hdpos
    rw [hcancel]
    exact Rat.le_trans (by grind) (Rat.mul_le_mul_of_nonneg_left hden hc)

theorem unit_chart_increment_bounds {u v : Rat}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    (v-u)/4 ≤ innerWedge u v ∧ outerWedge u v ≤ v-u := by
  have hv0 : 0 ≤ v := Rat.le_trans hu huv
  have hu1 : u ≤ 1 := Rat.le_trans huv hv
  have hd : 0 ≤ v-u := by grind
  have hsq0 := Rat.mul_nonneg hu hu
  have hsq1 := Rat.mul_nonneg hv0 hv0
  have hsqU : u*u ≤ 1 := by
    have h := Rat.mul_le_mul_of_nonneg_left hu1 hu
    grind
  have hsqV : v*v ≤ 1 := by
    have h := Rat.mul_le_mul_of_nonneg_left hv hv0
    grind
  have hden : 0 < (1+u*u)*(1+v*v) :=
    Rat.mul_pos (denominator_pos u) (denominator_pos v)
  have hden4 : (1+u*u)*(1+v*v) ≤ 4 := by
    have ha : 1+u*u ≤ 2 := by grind
    have hb : 1+v*v ≤ 2 := by grind
    have hb0 : 0 ≤ 1+v*v := by grind
    have h1 := Rat.mul_le_mul_of_nonneg_right ha hb0
    have h2 := Rat.mul_le_mul_of_nonneg_left hb (by decide +kernel : (0:Rat)≤2)
    grind
  have huv0 := Rat.mul_nonneg hu hv0
  have h01 : 0 < 1+u*v := by grind
  have hi := Rat.div_mul_cancel (a:=(v-u)*(1+u*v)) (Rat.ne_of_gt hden)
  have ho := Rat.div_mul_cancel (a:=v-u) (Rat.ne_of_gt h01)
  unfold innerWedge outerWedge
  constructor
  · apply Rat.le_of_mul_le_mul_right (c:=(1+u*u)*(1+v*v)) _ hden
    rw [hi]
    have hmul := Rat.mul_le_mul_of_nonneg_left hden4 hd
    have hmul2 := Rat.mul_nonneg hd huv0
    grind
  · apply Rat.le_of_mul_le_mul_right (c:=1+u*v) _ h01
    rw [ho]
    have hmul := Rat.mul_nonneg hd huv0
    grind

def lowerFan (h : Rat) : Nat → Rat
  | 0 => 0
  | n+1 => lowerFan h n+innerWedge ((n:Rat)*h) (((n+1:Nat):Rat)*h)

def upperFan (h : Rat) : Nat → Rat
  | 0 => 0
  | n+1 => upperFan h n+outerWedge ((n:Rat)*h) (((n+1:Nat):Rat)*h)

theorem fan_gap_bound (h : Rat) (hh : 0 ≤ h) (n : Nat) :
    0 ≤ upperFan h n-lowerFan h n ∧
      upperFan h n-lowerFan h n ≤ (n:Rat)*h*h*h := by
  induction n with
  | zero =>
    simp [upperFan,lowerFan]
    constructor <;> decide +kernel
  | succ n ih =>
    have hn0 : 0 ≤ (n:Rat) := by exact_mod_cast Nat.zero_le n
    have hu := Rat.mul_nonneg hn0 hh
    have hn : ((n+1:Nat):Rat)=(n:Rat)+1 := by simp
    have huv : (n:Rat)*h ≤ ((n+1:Nat):Rat)*h := by rw [hn]; grind
    have hg := wedge_gap_bounds hu huv
    simp only [upperFan,lowerFan]
    rw [hn] at hg ⊢
    constructor <;> grind

theorem uniform_fan_gap_bound (r : Rat) (hr : 0 ≤ r) (N : Nat) (hN : 0 < N) :
    0 ≤ upperFan (r/(N:Rat)) N-lowerFan (r/(N:Rat)) N ∧
      upperFan (r/(N:Rat)) N-lowerFan (r/(N:Rat)) N ≤
        r*r*r/((N:Rat)*(N:Rat)) := by
  have hn : 0 < (N:Rat) := by exact_mod_cast hN
  have hh : 0 ≤ r/(N:Rat) := Rat.mul_nonneg hr
    (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  have h := fan_gap_bound (r/(N:Rat)) hh N
  have hc := Rat.div_mul_cancel (a:=r) (Rat.ne_of_gt hn)
  have hn2 := Rat.mul_pos hn hn
  have hc2 := Rat.div_mul_cancel (a:=r*r*r) (Rat.ne_of_gt hn2)
  constructor
  · exact h.1
  · have heq : (N:Rat)*(r/(N:Rat))*(r/(N:Rat))*(r/(N:Rat))=
        r*r*r/((N:Rat)*(N:Rat)) := by grind
    rw [heq] at h
    exact h.2

end ComputableAnalysis.RationalAreaFoundation
