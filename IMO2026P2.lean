import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine

noncomputable section S

namespace IMO2026P2

abbrev Point := EuclideanSpace ℝ (Fin 2)

def StrictlyInsideTriangle (P X Y Z : Point) : Prop :=
  AffineIndependent ℝ ![X, Y, Z] ∧
    ∃ α β γ : ℝ,
      0 < α ∧ 0 < β ∧ 0 < γ ∧
        α + β + γ = 1 ∧
        P = α • X + β • Y + γ • Z

open scoped EuclideanSpace EuclideanGeometry RealInnerProductSpace

local instance : Module.Oriented ℝ Point (Fin 2) where
  positiveOrientation :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

private abbrev planeOrientation : Orientation ℝ Point (Fin 2) :=
  Module.Oriented.positiveOrientation

private def cross (u v : Point) : ℝ :=
  u 0 * v 1 - u 1 * v 0

private lemma planeOrientation_areaForm (u v : Point) :
    planeOrientation.areaForm u v = cross u v := by
  rw [Orientation.areaForm_to_volumeForm]
  rw [planeOrientation.volumeForm_robust
    (EuclideanSpace.basisFun (Fin 2) ℝ) rfl]
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [cross, Module.Basis.toMatrix_apply, mul_comm]

private lemma areaForm_sign_eq_of_cross_mul_pos {u v x y : Point}
    (h : 0 < cross u v * cross x y) :
    SignType.sign (planeOrientation.areaForm u v) =
      SignType.sign (planeOrientation.areaForm x y) := by
  rw [planeOrientation_areaForm, planeOrientation_areaForm]
  rcases mul_pos_iff.mp h with h | h
  · rw [sign_pos h.1, sign_pos h.2]
  · rw [sign_neg h.1, sign_neg h.2]

private lemma sign_oangle_eq_sign_areaForm {u v : Point}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    (planeOrientation.oangle u v).sign =
      SignType.sign (planeOrientation.areaForm u v) := by
  rw [Real.Angle.sign, Orientation.oangle, Real.Angle.sin_coe,
    Complex.sin_arg, planeOrientation.kahler_apply_apply]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.smul_im,
    Complex.I_im, zero_add, smul_eq_mul, mul_one]
  have hnorm :
      0 < ‖((inner ℝ u v : ℝ) : ℂ) +
        planeOrientation.areaForm u v • Complex.I‖ := by
    rw [← planeOrientation.kahler_apply_apply]
    exact norm_pos_iff.mpr (planeOrientation.kahler_ne_zero hu hv)
  rw [div_eq_mul_inv, sign_mul, sign_pos (inv_pos.mpr hnorm), mul_one]

private structure RayCrossIdentities
    (X Y Z P : Point) (α β γ : ℝ) : Prop where
  atX_Z : cross (P - X) (Z - X) = β * cross (Y - X) (Z - X)
  atX_Y : cross (P - X) (Y - X) = -γ * cross (Y - X) (Z - X)
  atY_X : cross (P - Y) (X - Y) = γ * cross (Y - X) (Z - X)
  atY_Z : cross (P - Y) (Z - Y) = -α * cross (Y - X) (Z - X)
  atZ_Y : cross (P - Z) (Y - Z) = α * cross (Y - X) (Z - X)
  atZ_X : cross (P - Z) (X - Z) = -β * cross (Y - X) (Z - X)

private lemma barycentric_cross_identities {X Y Z P : Point} {α β γ : ℝ}
    (hP : P = α • X + β • Y + γ • Z)
    (hsum : α + β + γ = 1) :
    RayCrossIdentities X Y Z P α β γ := by
  have hP0 := congrArg (fun Q : Point => Q 0) hP
  have hP1 := congrArg (fun Q : Point => Q 1) hP
  change P 0 = α * X 0 + β * Y 0 + γ * Z 0 at hP0
  change P 1 = α * X 1 + β * Y 1 + γ * Z 1 at hP1
  constructor
  · change (P 0 - X 0) * (Z 1 - X 1) - (P 1 - X 1) * (Z 0 - X 0) =
      β * ((Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0))
    rw [hP0, hP1]
    linear_combination (X 0 * Z 1 - X 1 * Z 0) * hsum
  · change (P 0 - X 0) * (Y 1 - X 1) - (P 1 - X 1) * (Y 0 - X 0) =
      -γ * ((Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0))
    rw [hP0, hP1]
    linear_combination (X 0 * Y 1 - X 1 * Y 0) * hsum
  · change (P 0 - Y 0) * (X 1 - Y 1) - (P 1 - Y 1) * (X 0 - Y 0) =
      γ * ((Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0))
    rw [hP0, hP1]
    linear_combination -(X 0 * Y 1 - X 1 * Y 0) * hsum
  · change (P 0 - Y 0) * (Z 1 - Y 1) - (P 1 - Y 1) * (Z 0 - Y 0) =
      -α * ((Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0))
    rw [hP0, hP1]
    linear_combination (Y 0 * Z 1 - Y 1 * Z 0) * hsum
  · change (P 0 - Z 0) * (Y 1 - Z 1) - (P 1 - Z 1) * (Y 0 - Z 0) =
      α * ((Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0))
    rw [hP0, hP1]
    linear_combination -(Y 0 * Z 1 - Y 1 * Z 0) * hsum
  · change (P 0 - Z 0) * (X 1 - Z 1) - (P 1 - Z 1) * (X 0 - Z 0) =
      -β * ((Y 0 - X 0) * (Z 1 - X 1) - (Y 1 - X 1) * (Z 0 - X 0))
    rw [hP0, hP1]
    linear_combination -(X 0 * Z 1 - X 1 * Z 0) * hsum

private lemma cross_ne_zero_of_affineIndependent
    {X Y Z : Point} (h : AffineIndependent ℝ ![X, Y, Z]) :
    cross (Y - X) (Z - X) ≠ 0 := by
  have hYX : Y ≠ X := by
    intro hYX
    have hi : (1 : Fin 3) = 0 := h.injective (by simpa using hYX)
    omega
  have hZX : Z ≠ X := by
    intro hZX
    have hi : (2 : Fin 3) = 0 := h.injective (by simpa using hZX)
    omega
  have hXY : Y - X ≠ 0 := sub_ne_zero.mpr hYX
  have hXZ : Z - X ≠ 0 := sub_ne_zero.mpr hZX
  have hnotcol : ¬ Collinear ℝ ({X, Y, Z} : Set Point) :=
    affineIndependent_iff_not_collinear_set.mp h
  have hsign : (planeOrientation.oangle (Y - X) (Z - X)).sign ≠ 0 := by
    intro hs
    have hs' : (∡ Y X Z).sign = 0 := by
      simpa [EuclideanGeometry.oangle] using hs
    have hcol : Collinear ℝ ({Y, X, Z} : Set Point) :=
      (EuclideanGeometry.oangle_sign_eq_zero_iff_collinear
        (p₁ := Y) (p₂ := X) (p₃ := Z)).mp hs'
    apply hnotcol
    have hset : ({X, Z, Y} : Set Point) = {X, Y, Z} := by
      ext w
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto
    rw [Set.insert_comm, Set.pair_comm] at hcol
    rwa [hset] at hcol
  rw [sign_oangle_eq_sign_areaForm hXY hXZ,
    planeOrientation_areaForm] at hsign
  exact fun hc => hsign (by rw [hc, sign_zero])

private lemma oangle_eq_of_angle_eq_of_area_sign_eq {u v x y : Point}
    (hu : u ≠ 0) (hv : v ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hangle : InnerProductGeometry.angle u v =
      InnerProductGeometry.angle x y)
    (hsign : SignType.sign (planeOrientation.areaForm u v) =
      SignType.sign (planeOrientation.areaForm x y)) :
    planeOrientation.oangle u v = planeOrientation.oangle x y := by
  apply planeOrientation.oangle_eq_of_angle_eq_of_sign_eq hangle
  rw [sign_oangle_eq_sign_areaForm hu hv,
    sign_oangle_eq_sign_areaForm hx hy]
  exact hsign

private lemma cross_swap (u v : Point) : cross u v = -cross v u := by
  simp only [cross]
  ring

private lemma midpoint_BMC_cross (A B C : Point) :
    cross (midpoint ℝ A B - B) (C - B) =
      -(1 / 2 : ℝ) * cross (B - A) (C - A) := by
  change
    (midpoint ℝ A B 0 - B 0) * (C 1 - B 1) -
        (midpoint ℝ A B 1 - B 1) * (C 0 - B 0) =
      -(1 / 2 : ℝ) *
        ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0))
  simp only [midpoint_eq_smul_add, invOf_eq_inv]
  change
    ((2 : ℝ)⁻¹ * (A 0 + B 0) - B 0) * (C 1 - B 1) -
        ((2 : ℝ)⁻¹ * (A 1 + B 1) - B 1) * (C 0 - B 0) =
      -(1 / 2 : ℝ) *
        ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0))
  ring

private lemma midpoint_BNC_cross (A B C : Point) :
    cross (midpoint ℝ A C - B) (C - B) =
      -(1 / 2 : ℝ) * cross (B - A) (C - A) := by
  change
    (midpoint ℝ A C 0 - B 0) * (C 1 - B 1) -
        (midpoint ℝ A C 1 - B 1) * (C 0 - B 0) =
      -(1 / 2 : ℝ) *
        ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0))
  simp only [midpoint_eq_smul_add, invOf_eq_inv]
  change
    ((2 : ℝ)⁻¹ * (A 0 + C 0) - B 0) * (C 1 - B 1) -
        ((2 : ℝ)⁻¹ * (A 1 + C 1) - B 1) * (C 0 - B 0) =
      -(1 / 2 : ℝ) *
        ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0))
  ring

private lemma ABL_cross_of_BNC_barycentric
    {A B C L : Point} {α β γ : ℝ}
    (hL : L = α • B + β • midpoint ℝ A C + γ • C)
    (hsum : α + β + γ = 1) :
    cross (B - A) (L - A) =
      (β / 2 + γ) * cross (B - A) (C - A) := by
  have hL0 := congrArg (fun Q : Point => Q 0) hL
  have hL1 := congrArg (fun Q : Point => Q 1) hL
  change L 0 = α * B 0 + β * midpoint ℝ A C 0 + γ * C 0 at hL0
  change L 1 = α * B 1 + β * midpoint ℝ A C 1 + γ * C 1 at hL1
  have hα : α = 1 - β - γ := by linarith
  change
    (B 0 - A 0) * (L 1 - A 1) - (B 1 - A 1) * (L 0 - A 0) =
      (β / 2 + γ) *
        ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0))
  rw [hL0, hL1, hα]
  simp only [midpoint_eq_smul_add, invOf_eq_inv]
  change
    (B 0 - A 0) *
          ((1 - β - γ) * B 1 + β * ((2 : ℝ)⁻¹ * (A 1 + C 1)) + γ * C 1 - A 1) -
        (B 1 - A 1) *
          ((1 - β - γ) * B 0 + β * ((2 : ℝ)⁻¹ * (A 0 + C 0)) + γ * C 0 - A 0) =
      (β / 2 + γ) *
        ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0))
  ring

private lemma AKC_cross_of_BMC_barycentric
    {A B C K : Point} {α β γ : ℝ}
    (hK : K = α • B + β • midpoint ℝ A B + γ • C)
    (hsum : α + β + γ = 1) :
    cross (K - A) (C - A) =
      (α + β / 2) * cross (B - A) (C - A) := by
  have hK0 := congrArg (fun Q : Point => Q 0) hK
  have hK1 := congrArg (fun Q : Point => Q 1) hK
  change K 0 = α * B 0 + β * midpoint ℝ A B 0 + γ * C 0 at hK0
  change K 1 = α * B 1 + β * midpoint ℝ A B 1 + γ * C 1 at hK1
  have hγ : γ = 1 - α - β := by linarith
  change
    (K 0 - A 0) * (C 1 - A 1) - (K 1 - A 1) * (C 0 - A 0) =
      (α + β / 2) *
        ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0))
  rw [hK0, hK1, hγ]
  simp only [midpoint_eq_smul_add, invOf_eq_inv]
  change
    (α * B 0 + β * ((2 : ℝ)⁻¹ * (A 0 + B 0)) + (1 - α - β) * C 0 - A 0) *
          (C 1 - A 1) -
        (α * B 1 + β * ((2 : ℝ)⁻¹ * (A 1 + B 1)) + (1 - α - β) * C 1 - A 1) *
          (C 0 - A 0) =
      (α + β / 2) *
        ((B 0 - A 0) * (C 1 - A 1) - (B 1 - A 1) * (C 0 - A 0))
  ring

private lemma left_ne_zero_of_cross_ne_zero {u v : Point}
    (h : cross u v ≠ 0) : u ≠ 0 := by
  intro hu
  apply h
  simp [hu, cross]

private lemma right_ne_zero_of_cross_ne_zero {u v : Point}
    (h : cross u v ≠ 0) : v ≠ 0 := by
  intro hv
  apply h
  simp [hv, cross]

private lemma positive_scaled_square {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : d ≠ 0) :
    0 < (a * d) * (b * d) := by
  calc
    0 < (a * b) * (d * d) := mul_pos (mul_pos ha hb) (mul_self_pos.mpr hd)
    _ = (a * d) * (b * d) := by ring

/-- The specialized orientation bridge needed by the faithful P2 angle proof. -/
private theorem p2_sign_bridge
    (A B C K L : Point)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hK_BMC : StrictlyInsideTriangle K B (midpoint ℝ A B) C)
    (hL_BNC : StrictlyInsideTriangle L B (midpoint ℝ A C) C)
    (hK_ABL : StrictlyInsideTriangle K A B L)
    (hL_AKC : StrictlyInsideTriangle L A K C) :
    cross (B - A) (C - A) ≠ 0 ∧
    SignType.sign (planeOrientation.areaForm (K - B) (A - B)) =
      SignType.sign (planeOrientation.areaForm (A - C) (L - C)) ∧
    SignType.sign (planeOrientation.areaForm (L - B) (K - B)) =
      SignType.sign (planeOrientation.areaForm
        (L - midpoint ℝ A C) (C - midpoint ℝ A C)) ∧
    SignType.sign (planeOrientation.areaForm (L - C) (K - C)) =
      SignType.sign (planeOrientation.areaForm
        (B - midpoint ℝ A B) (K - midpoint ℝ A B)) ∧
    K - B ≠ 0 ∧ A - B ≠ 0 ∧ A - C ≠ 0 ∧ L - C ≠ 0 ∧
    L - B ≠ 0 ∧ K - B ≠ 0 ∧
      L - midpoint ℝ A C ≠ 0 ∧ C - midpoint ℝ A C ≠ 0 ∧
    L - C ≠ 0 ∧ K - C ≠ 0 ∧
      B - midpoint ℝ A B ≠ 0 ∧ K - midpoint ℝ A B ≠ 0 := by
  rcases hK_BMC.2 with ⟨kB, kM, kC, hkB, hkM, hkC, hkSum, hK⟩
  rcases hL_BNC.2 with ⟨lB, lN, lC, hlB, hlN, hlC, hlSum, hL⟩
  rcases hK_ABL.2 with ⟨qA, qB, qL, hqA, hqB, hqL, hqSum, hK'⟩
  rcases hL_AKC.2 with ⟨rA, rK, rC, hrA, hrK, hrC, hrSum, hL'⟩
  let D := cross (B - A) (C - A)
  have hD : D ≠ 0 := cross_ne_zero_of_affineIndependent hABC
  have hkIds := barycentric_cross_identities hK hkSum
  have hlIds := barycentric_cross_identities hL hlSum
  have hqIds := barycentric_cross_identities hK' hqSum
  have hrIds := barycentric_cross_identities hL' hrSum
  have hBMC : cross (midpoint ℝ A B - B) (C - B) = -(1 / 2 : ℝ) * D := by
    exact midpoint_BMC_cross A B C
  have hBNC : cross (midpoint ℝ A C - B) (C - B) = -(1 / 2 : ℝ) * D := by
    exact midpoint_BNC_cross A B C
  have hABL : cross (B - A) (L - A) = (lN / 2 + lC) * D := by
    exact ABL_cross_of_BNC_barycentric hL hlSum
  have hAKC : cross (K - A) (C - A) = (kB + kM / 2) * D := by
    exact AKC_cross_of_BMC_barycentric hK hkSum
  have hf₁₁ : cross (K - B) (A - B) = qL * (lN / 2 + lC) * D := by
    rw [hqIds.atY_X, hABL]
    ring
  have hf₁₂ : cross (A - C) (L - C) = rK * (kB + kM / 2) * D := by
    rw [cross_swap, hrIds.atZ_X, hAKC]
    ring
  have hf₂₁ : cross (L - B) (K - B) = qA * (lN / 2 + lC) * D := by
    rw [cross_swap, hqIds.atY_Z, hABL]
    ring
  have hf₂₂ : cross (L - midpoint ℝ A C) (C - midpoint ℝ A C) =
      (lB / 2) * D := by
    rw [hlIds.atY_Z, hBNC]
    ring
  have hf₃₁ : cross (L - C) (K - C) = rA * (kB + kM / 2) * D := by
    rw [hrIds.atZ_Y, hAKC]
    ring
  have hf₃₂ : cross (B - midpoint ℝ A B) (K - midpoint ℝ A B) =
      (kC / 2) * D := by
    rw [cross_swap, hkIds.atY_X, hBMC]
    ring
  have hsumL : 0 < lN / 2 + lC := by positivity
  have hsumK : 0 < kB + kM / 2 := by positivity
  have hp₁ : 0 < cross (K - B) (A - B) * cross (A - C) (L - C) := by
    rw [hf₁₁, hf₁₂]
    exact positive_scaled_square (mul_pos hqL hsumL) (mul_pos hrK hsumK) hD
  have hp₂ : 0 < cross (L - B) (K - B) *
      cross (L - midpoint ℝ A C) (C - midpoint ℝ A C) := by
    rw [hf₂₁, hf₂₂]
    exact positive_scaled_square (mul_pos hqA hsumL) (by positivity) hD
  have hp₃ : 0 < cross (L - C) (K - C) *
      cross (B - midpoint ℝ A B) (K - midpoint ℝ A B) := by
    rw [hf₃₁, hf₃₂]
    exact positive_scaled_square (mul_pos hrA hsumK) (by positivity) hD
  have hc₁₁ : cross (K - B) (A - B) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hp₁
    exact (lt_irrefl 0) hp₁
  have hc₁₂ : cross (A - C) (L - C) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hp₁
    exact (lt_irrefl 0) hp₁
  have hc₂₁ : cross (L - B) (K - B) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hp₂
    exact (lt_irrefl 0) hp₂
  have hc₂₂ : cross (L - midpoint ℝ A C) (C - midpoint ℝ A C) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hp₂
    exact (lt_irrefl 0) hp₂
  have hc₃₁ : cross (L - C) (K - C) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hp₃
    exact (lt_irrefl 0) hp₃
  have hc₃₂ : cross (B - midpoint ℝ A B) (K - midpoint ℝ A B) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hp₃
    exact (lt_irrefl 0) hp₃
  exact ⟨hD,
    areaForm_sign_eq_of_cross_mul_pos hp₁,
    areaForm_sign_eq_of_cross_mul_pos hp₂,
    areaForm_sign_eq_of_cross_mul_pos hp₃,
    left_ne_zero_of_cross_ne_zero hc₁₁,
    right_ne_zero_of_cross_ne_zero hc₁₁,
    left_ne_zero_of_cross_ne_zero hc₁₂,
    right_ne_zero_of_cross_ne_zero hc₁₂,
    left_ne_zero_of_cross_ne_zero hc₂₁,
    right_ne_zero_of_cross_ne_zero hc₂₁,
    left_ne_zero_of_cross_ne_zero hc₂₂,
    right_ne_zero_of_cross_ne_zero hc₂₂,
    left_ne_zero_of_cross_ne_zero hc₃₁,
    right_ne_zero_of_cross_ne_zero hc₃₁,
    left_ne_zero_of_cross_ne_zero hc₃₂,
    right_ne_zero_of_cross_ne_zero hc₃₂⟩

set_option maxHeartbeats 800000 in
private theorem p2_polynomial_certificate
    (A B C beta rho lam mu x y u v H : ℝ)
    (hbeta : 0 < beta) (hrho : 0 < rho)
    (hlam : 0 < lam) (hmu : 0 < mu)
    (hbeta_lam : beta + lam < 1) (hmu_rho : mu + rho < 1)
    (hx : x = beta + lam * u) (hy : y = lam * v)
    (hu : u = mu * x) (hv : v = mu * y + rho)
    (hangle₁ : A * u * x - A * u - C * v * y + C * y = 0)
    (hangle₂ :
      -(2 * A * u ^ 2 * x - 2 * A * u ^ 2 - 2 * A * u * x + 2 * A * u +
        4 * B * u * v * x - 4 * B * u * v + C * u * y +
        2 * C * v ^ 2 * x - 2 * C * v ^ 2 - C * v * x +
        2 * C * v * y + C * v - C * y) = 0)
    (hangle₃ :
      -(2 * A * u * x + A * u * y - A * u + 2 * A * v * x ^ 2 -
        A * v * x - 2 * A * x ^ 2 + A * x + 4 * B * v * x * y -
        4 * B * x * y + 2 * C * v * y ^ 2 - 2 * C * v * y -
        2 * C * y ^ 2 + 2 * C * y) = 0)
    (hH : H =
      2 * A * u ^ 2 * x + 2 * A * u ^ 2 * y - 2 * A * u * x ^ 2 -
      A * u * y - 2 * A * v * x ^ 2 + A * v * x +
      4 * B * u * v * x + 4 * B * u * v * y - 4 * B * u * x * y -
      4 * B * v * x * y - 2 * C * u * y ^ 2 + C * u * y +
      2 * C * v ^ 2 * x + 2 * C * v ^ 2 * y - C * v * x -
      2 * C * v * y ^ 2) :
    H = 0 := by
  have hmu_lt : mu < 1 := by linarith
  have hlam_lt : lam < 1 := by linarith
  have hlam_mu_gap : 0 < lam * (1 - mu) :=
    mul_pos hlam (by linarith)
  have hmu_lam_gap : 0 < mu * (1 - lam) :=
    mul_pos hmu (by linarith)
  have hx_pos : 0 < x := by nlinarith
  have hx_lt : x < 1 := by nlinarith
  have hv_pos : 0 < v := by nlinarith
  have hv_lt : v < 1 := by nlinarith
  let E₁ : ℝ := A * u * x - A * u - C * v * y + C * y
  let E₂ : ℝ :=
    -(2 * A * u ^ 2 * x - 2 * A * u ^ 2 - 2 * A * u * x + 2 * A * u +
      4 * B * u * v * x - 4 * B * u * v + C * u * y +
      2 * C * v ^ 2 * x - 2 * C * v ^ 2 - C * v * x +
      2 * C * v * y + C * v - C * y)
  let E₃ : ℝ :=
    -(2 * A * u * x + A * u * y - A * u + 2 * A * v * x ^ 2 -
      A * v * x - 2 * A * x ^ 2 + A * x + 4 * B * v * x * y -
      4 * B * x * y + 2 * C * v * y ^ 2 - 2 * C * v * y -
      2 * C * y ^ 2 + 2 * C * y)
  have hE₁ : E₁ = 0 := by simpa [E₁] using hangle₁
  have hE₂ : E₂ = 0 := by simpa [E₂] using hangle₂
  have hE₃ : E₃ = 0 := by simpa [E₃] using hangle₃
  have hcert : (v - 1) * (x - 1) * H = 0 := by
    calc
      (v - 1) * (x - 1) * H =
          (lam * mu * v * x + 2 * lam * v ^ 2 - lam * v +
              2 * mu * x ^ 2 - mu * x + 3 * v * x - v - x) * E₁ -
            (v - 1) * (lam * v + x) * E₂ +
            (x - 1) * (mu * x + v) * E₃ := by
              simp only [E₁, E₂, E₃]
              rw [hH, hu, hy]
              ring
      _ = 0 := by rw [hE₁, hE₂, hE₃]; ring
  have hfactor : 0 < (v - 1) * (x - 1) := by nlinarith
  nlinarith

/-- Circumcenter equalities imply the numerator used above is exactly
`(x*v-y*u)` times the target midpoint-distance equation. -/
private theorem p2_circumcenter_syzygy
    (A B C x y u v p q H : ℝ)
    (hK : 2 * (x * p + y * q) =
      A * x ^ 2 + 2 * B * x * y + C * y ^ 2)
    (hL : 2 * (u * p + v * q) =
      A * u ^ 2 + 2 * B * u * v + C * v ^ 2)
    (hH : H =
      2 * A * u ^ 2 * x + 2 * A * u ^ 2 * y - 2 * A * u * x ^ 2 -
      A * u * y - 2 * A * v * x ^ 2 + A * v * x +
      4 * B * u * v * x + 4 * B * u * v * y - 4 * B * u * x * y -
      4 * B * v * x * y - 2 * C * u * y ^ 2 + C * u * y +
      2 * C * v ^ 2 * x + 2 * C * v ^ 2 * y - C * v * x -
      2 * C * v * y ^ 2) :
    (x * v - y * u) * (A - C - 4 * p + 4 * q) = H := by
  rw [hH]
  calc
    (x * v - y * u) * (A - C - 4 * p + 4 * q) =
        2 * A * u ^ 2 * x + 2 * A * u ^ 2 * y - 2 * A * u * x ^ 2 -
        A * u * y - 2 * A * v * x ^ 2 + A * v * x +
        4 * B * u * v * x + 4 * B * u * v * y - 4 * B * u * x * y -
        4 * B * v * x * y - 2 * C * u * y ^ 2 + C * u * y +
        2 * C * v ^ 2 * x + 2 * C * v ^ 2 * y - C * v * x -
        2 * C * v * y ^ 2 +
        (-2 * u - 2 * v) *
          (2 * (x * p + y * q) -
            (A * x ^ 2 + 2 * B * x * y + C * y ^ 2)) +
        (2 * x + 2 * y) *
          (2 * (u * p + v * q) -
            (A * u ^ 2 + 2 * B * u * v + C * v ^ 2)) := by ring
    _ = _ := by rw [hK, hL]; ring

/-- Positive nested parameters make the affine determinant nonzero, so the
numerator certificate yields equal distances from the circumcenter to the two
midpoints. -/
private theorem p2_target_from_certificates
    (A C beta lam x y u v p q H : ℝ)
    (hbeta : 0 < beta)
    (hx : x = beta + lam * u) (hy : y = lam * v)
    (hH : H = 0)
    (hv_pos : 0 < v)
    (hcenter : (x * v - y * u) * (A - C - 4 * p + 4 * q) = H) :
    A - C - 4 * p + 4 * q = 0 := by
  have hdet : 0 < x * v - y * u := by
    rw [hx, hy]
    nlinarith [mul_pos hbeta hv_pos]
  nlinarith

private abbrev Coeff := ℝ × ℝ

/-- The linear combination with coefficient pair `(a, b)` relative to `U, V`. -/
private def lincomb (U V : Point) (a b : ℝ) : Point := a • U + b • V

/-- The determinant of two coefficient pairs. -/
private def detCoeff (p q : Coeff) : ℝ := p.1 * q.2 - p.2 * q.1

/-- The Gram bilinear form on coefficient pairs induced by `U, V`. -/
private def gram (U V : Point) (p q : Coeff) : ℝ :=
  p.1 * q.1 * inner ℝ U U +
    (p.1 * q.2 + p.2 * q.1) * inner ℝ U V +
      p.2 * q.2 * inner ℝ V V

/-- Bilinearity of the standard area form, expressed in coefficients. -/
private theorem areaForm_lincomb (U V : Point) (a b c d : ℝ) :
    planeOrientation.areaForm (lincomb U V a b) (lincomb U V c d) =
      (a * d - b * c) * planeOrientation.areaForm U V := by
  simp only [lincomb, map_add, map_smul, smul_eq_mul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Orientation.areaForm_apply_self]
  rw [planeOrientation.areaForm_swap V U]
  ring

/-- Bilinearity of `cross`, expressed in coefficients. -/
private theorem cross_lincomb (U V : Point) (a b c d : ℝ) :
    cross (lincomb U V a b) (lincomb U V c d) =
      (a * d - b * c) * cross U V := by
  rw [← planeOrientation_areaForm, areaForm_lincomb,
    planeOrientation_areaForm]

/-- The inner product of two linear combinations is their coefficient Gram form. -/
private theorem inner_lincomb (U V : Point) (a b c d : ℝ) :
    inner ℝ (lincomb U V a b) (lincomb U V c d) =
      gram U V (a, b) (c, d) := by
  simp only [lincomb, gram, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_trivial]
  rw [real_inner_comm V U]
  ring

/-- Oriented area is the norm product times the sine of the oriented angle. -/
private theorem cross_eq_norm_mul_norm_mul_sin_oangle (p q : Point) :
    cross p q = ‖p‖ * ‖q‖ * Real.Angle.sin (planeOrientation.oangle p q) := by
  rw [← planeOrientation_areaForm, Orientation.oangle, Real.Angle.sin_coe]
  rw [← planeOrientation.norm_kahler p q]
  rw [Complex.norm_mul_sin_arg]
  simp [Orientation.kahler_apply_apply]

/-- Equal oriented angles give the cross/inner polynomial identity. -/
private theorem cross_mul_inner_eq_inner_mul_cross_of_oangle_eq
    {p q r s : Point}
    (h : planeOrientation.oangle p q = planeOrientation.oangle r s) :
    cross p q * inner ℝ r s = inner ℝ p q * cross r s := by
  rw [cross_eq_norm_mul_norm_mul_sin_oangle,
    planeOrientation.inner_eq_norm_mul_norm_mul_cos_oangle,
    planeOrientation.inner_eq_norm_mul_norm_mul_cos_oangle,
    cross_eq_norm_mul_norm_mul_sin_oangle, h]
  ring

/-- For four nonzero coefficient vectors, equal oriented angles become a coefficient identity
once the nondegenerate base area is cancelled. -/
private theorem detCoeff_mul_gram_eq_gram_mul_detCoeff_of_oangle_eq
    {U V : Point} {p q r s : Coeff}
    (hUV : cross U V ≠ 0)
    (hangle : planeOrientation.oangle (lincomb U V p.1 p.2) (lincomb U V q.1 q.2) =
      planeOrientation.oangle (lincomb U V r.1 r.2) (lincomb U V s.1 s.2)) :
    detCoeff p q * gram U V r s = gram U V p q * detCoeff r s := by
  have h := cross_mul_inner_eq_inner_mul_cross_of_oangle_eq hangle
  rw [cross_lincomb, cross_lincomb, inner_lincomb, inner_lincomb] at h
  simp only [detCoeff] at h ⊢
  apply mul_left_cancel₀ hUV
  linear_combination h

private theorem p2_circumcenter_equations
    (U V A K L O : Point) (x y u v : ℝ)
    (hK : K = A + x • U + y • V)
    (hL : L = A + u • U + v • V)
    (hO : dist O A = dist O K ∧ dist O A = dist O L) :
    (2 * (x * ⟪O - A, U⟫ + y * ⟪O - A, V⟫) =
      x ^ 2 * ⟪U, U⟫ + 2 * x * y * ⟪U, V⟫ + y ^ 2 * ⟪V, V⟫) ∧
    (2 * (u * ⟪O - A, U⟫ + v * ⟪O - A, V⟫) =
      u ^ 2 * ⟪U, U⟫ + 2 * u * v * ⟪U, V⟫ + v ^ 2 * ⟪V, V⟫) := by
  have hOK' : ⟪O - A, O - A⟫ = ⟪O - K, O - K⟫ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      ← dist_eq_norm, ← dist_eq_norm]
    exact congrArg (fun t : ℝ => t ^ 2) hO.1
  have hOL' : ⟪O - A, O - A⟫ = ⟪O - L, O - L⟫ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      ← dist_eq_norm, ← dist_eq_norm]
    exact congrArg (fun t : ℝ => t ^ 2) hO.2
  have hKsub : O - K = (O - A) - (x • U + y • V) := by
    rw [hK]
    abel
  have hLsub : O - L = (O - A) - (u • U + v • V) := by
    rw [hL]
    abel
  rw [hKsub] at hOK'
  rw [hLsub] at hOL'
  constructor
  · simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_right, real_inner_comm] at hOK' ⊢
    ring_nf at hOK' ⊢
    linarith [hOK']
  · simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_right, real_inner_comm] at hOL' ⊢
    ring_nf at hOL' ⊢
    linarith [hOL']

/-- The scalar target is exactly equality of the distances from `O` to the two
unit-step midpoints based at `A`. -/
private theorem scalar_target_iff_midpoint_equidistant (U V A O : Point) :
    ⟪U, U⟫ - ⟪V, V⟫ - 4 * ⟪O - A, U⟫ + 4 * ⟪O - A, V⟫ = 0 ↔
      dist O (midpoint ℝ A (A + U)) = dist O (midpoint ℝ A (A + V)) := by
  have hmidU : midpoint ℝ A (A + U) = A + (2 : ℝ)⁻¹ • U := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    module
  have hmidV : midpoint ℝ A (A + V) = A + (2 : ℝ)⁻¹ • V := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    module
  have hUsq :
      dist O (midpoint ℝ A (A + U)) ^ 2 =
        ⟪(O - A) - (2 : ℝ)⁻¹ • U, (O - A) - (2 : ℝ)⁻¹ • U⟫ := by
    rw [hmidU, dist_eq_norm, ← real_inner_self_eq_norm_sq]
    apply congrArg (fun W : Point => ⟪W, W⟫)
    abel
  have hVsq :
      dist O (midpoint ℝ A (A + V)) ^ 2 =
        ⟪(O - A) - (2 : ℝ)⁻¹ • V, (O - A) - (2 : ℝ)⁻¹ • V⟫ := by
    rw [hmidV, dist_eq_norm, ← real_inner_self_eq_norm_sq]
    apply congrArg (fun W : Point => ⟪W, W⟫)
    abel
  rw [← sq_eq_sq₀ dist_nonneg dist_nonneg, hUsq, hVsq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_right, real_inner_comm]
  constructor <;> intro h <;> nlinarith

theorem imo2026_p2
    (A B C K L O : Point)
    (hABC : AffineIndependent ℝ ![A, B, C])
    (hK_BMC : StrictlyInsideTriangle K B (midpoint ℝ A B) C)
    (hL_BNC : StrictlyInsideTriangle L B (midpoint ℝ A C) C)
    (hK_ABL : StrictlyInsideTriangle K A B L)
    (hL_AKC : StrictlyInsideTriangle L A K C)
    (h₁ : EuclideanGeometry.angle K B A = EuclideanGeometry.angle A C L)
    (h₂ : EuclideanGeometry.angle L B K =
      EuclideanGeometry.angle L (midpoint ℝ A C) C)
    (h₃ : EuclideanGeometry.angle L C K =
      EuclideanGeometry.angle B (midpoint ℝ A B) K)
    (hO : dist O A = dist O K ∧ dist O A = dist O L) :
    dist O (midpoint ℝ A B) = dist O (midpoint ℝ A C) := by
  obtain ⟨hD, hs₁, hs₂, hs₃,
    hKB, hAB, hAC, hLC, hLB, hKB', hLN, hCN, hLC', hKC, hBM, hKM⟩ :=
    p2_sign_bridge A B C K L hABC hK_BMC hL_BNC hK_ABL hL_AKC
  have ho₁ : planeOrientation.oangle (K - B) (A - B) =
      planeOrientation.oangle (A - C) (L - C) :=
    oangle_eq_of_angle_eq_of_area_sign_eq hKB hAB hAC hLC h₁ hs₁
  have ho₂ : planeOrientation.oangle (L - B) (K - B) =
      planeOrientation.oangle (L - midpoint ℝ A C)
        (C - midpoint ℝ A C) :=
    oangle_eq_of_angle_eq_of_area_sign_eq hLB hKB' hLN hCN h₂ hs₂
  have ho₃ : planeOrientation.oangle (L - C) (K - C) =
      planeOrientation.oangle (B - midpoint ℝ A B)
        (K - midpoint ℝ A B) :=
    oangle_eq_of_angle_eq_of_area_sign_eq hLC' hKC hBM hKM h₃ hs₃
  rcases hK_BMC.2 with
    ⟨kB, kM, kC, hkB, hkM, hkC, hkSum, hKraw⟩
  rcases hL_BNC.2 with
    ⟨lB, lN, lC, hlB, hlN, hlC, hlSum, hLraw⟩
  let U : Point := B - A
  let V : Point := C - A
  let x : ℝ := kB + kM / 2
  let y : ℝ := kC
  let u : ℝ := lB
  let v : ℝ := lN / 2 + lC
  have hUV : cross U V ≠ 0 := by
    simpa [U, V] using hD
  have hv_pos : 0 < v := by
    dsimp [v]
    positivity
  have hKcoord : K = A + x • U + y • V := by
    rw [hKraw]
    dsimp [U, V, x, y]
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    norm_num
    have hkB' : kB = 1 - kM - kC := by linarith
    rw [hkB']
    module
  have hLcoord : L = A + u • U + v • V := by
    rw [hLraw]
    dsimp [U, V, u, v]
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    norm_num
    have hlB' : lB = 1 - lN - lC := by linarith
    rw [hlB']
    module
  have hcross_right (a b : ℝ) :
      cross (lincomb U V a b) V = a * cross U V := by
    simpa [lincomb] using cross_lincomb U V a b 0 1
  have hcross_left (a b : ℝ) :
      cross U (lincomb U V a b) = b * cross U V := by
    simpa [lincomb] using cross_lincomb U V 1 0 a b
  have hcoords_unique : ∀ {a b c d : ℝ},
      lincomb U V a b = lincomb U V c d → a = c ∧ b = d := by
    intro a b c d h
    have ha := congrArg (fun W : Point => cross W V) h
    have hb := congrArg (fun W : Point => cross U W) h
    change cross (lincomb U V a b) V = cross (lincomb U V c d) V at ha
    change cross U (lincomb U V a b) = cross U (lincomb U V c d) at hb
    rw [hcross_right, hcross_right] at ha
    rw [hcross_left, hcross_left] at hb
    constructor
    · exact mul_right_cancel₀ hUV ha
    · exact mul_right_cancel₀ hUV hb
  rcases hK_ABL.2 with
    ⟨kA, beta, lam, hkA, hbeta, hlam, hbetaLamSum, hKnested⟩
  have hKcoord' :
      K = A + (beta + lam * u) • U + (lam * v) • V := by
    rw [hKnested, hLcoord]
    have hkA' : kA = 1 - beta - lam := by linarith
    rw [hkA']
    module
  have hxyRay : x = beta + lam * u ∧ y = lam * v := by
    apply hcoords_unique
    have h := hKcoord.symm.trans hKcoord'
    apply add_left_cancel (a := A)
    simpa only [lincomb, add_assoc] using h
  have hbeta_lam : beta + lam < 1 := by linarith
  rcases hL_AKC.2 with
    ⟨lA, mu, rho, hlA, hmu, hrho, hmuRhoSum, hLnested⟩
  have hLcoord' :
      L = A + (mu * x) • U + (mu * y + rho) • V := by
    rw [hLnested, hKcoord]
    have hlA' : lA = 1 - mu - rho := by linarith
    rw [hlA']
    module
  have huvRay : u = mu * x ∧ v = mu * y + rho := by
    apply hcoords_unique
    have h := hLcoord.symm.trans hLcoord'
    apply add_left_cancel (a := A)
    simpa only [lincomb, add_assoc] using h
  have hmu_rho : mu + rho < 1 := by linarith
  have hKBcoord : K - B = lincomb U V (x - 1) y := by
    rw [hKcoord]
    dsimp [lincomb, U, V]
    module
  have hABcoord : A - B = lincomb U V (-1) 0 := by
    dsimp [lincomb, U, V]
    module
  have hACcoord : A - C = lincomb U V 0 (-1) := by
    dsimp [lincomb, U, V]
    module
  have hLCcoord : L - C = lincomb U V u (v - 1) := by
    rw [hLcoord]
    dsimp [lincomb, U, V]
    module
  have hLBcoord : L - B = lincomb U V (u - 1) v := by
    rw [hLcoord]
    dsimp [lincomb, U, V]
    module
  have hKCcoord : K - C = lincomb U V x (y - 1) := by
    rw [hKcoord]
    dsimp [lincomb, U, V]
    module
  have hLNcoord :
      L - midpoint ℝ A C = lincomb U V u (v - 1 / 2) := by
    rw [hLcoord]
    dsimp [lincomb, U, V]
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    norm_num
    module
  have hCNcoord :
      C - midpoint ℝ A C = lincomb U V 0 (1 / 2) := by
    dsimp [lincomb, U, V]
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    norm_num
    module
  have hBMcoord :
      B - midpoint ℝ A B = lincomb U V (1 / 2) 0 := by
    dsimp [lincomb, U, V]
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    norm_num
    module
  have hKMcoord :
      K - midpoint ℝ A B = lincomb U V (x - 1 / 2) y := by
    rw [hKcoord]
    dsimp [lincomb, U, V]
    simp only [midpoint_eq_smul_add, invOf_eq_inv]
    norm_num
    module
  have ho₁' := ho₁
  rw [hKBcoord, hABcoord, hACcoord, hLCcoord] at ho₁'
  have ho₂' := ho₂
  rw [hLBcoord, hKBcoord, hLNcoord, hCNcoord] at ho₂'
  have ho₃' := ho₃
  rw [hLCcoord, hKCcoord, hBMcoord, hKMcoord] at ho₃'
  have he₁ :
      detCoeff (x - 1, y) (-1, 0) * gram U V (0, -1) (u, v - 1) =
        gram U V (x - 1, y) (-1, 0) * detCoeff (0, -1) (u, v - 1) :=
    detCoeff_mul_gram_eq_gram_mul_detCoeff_of_oangle_eq
    (U := U) (V := V)
    (p := (x - 1, y)) (q := (-1, 0))
    (r := (0, -1)) (s := (u, v - 1))
    hUV ho₁'
  have he₂ :
      detCoeff (u - 1, v) (x - 1, y) *
          gram U V (u, v - 1 / 2) (0, 1 / 2) =
        gram U V (u - 1, v) (x - 1, y) *
          detCoeff (u, v - 1 / 2) (0, 1 / 2) :=
    detCoeff_mul_gram_eq_gram_mul_detCoeff_of_oangle_eq
    (U := U) (V := V)
    (p := (u - 1, v)) (q := (x - 1, y))
    (r := (u, v - 1 / 2)) (s := (0, 1 / 2))
    hUV ho₂'
  have he₃ :
      detCoeff (u, v - 1) (x, y - 1) *
          gram U V (1 / 2, 0) (x - 1 / 2, y) =
        gram U V (u, v - 1) (x, y - 1) *
          detCoeff (1 / 2, 0) (x - 1 / 2, y) :=
    detCoeff_mul_gram_eq_gram_mul_detCoeff_of_oangle_eq
    (U := U) (V := V)
    (p := (u, v - 1)) (q := (x, y - 1))
    (r := (1 / 2, 0)) (s := (x - 1 / 2, y))
    hUV ho₃'
  let gA : ℝ := inner ℝ U U
  let gB : ℝ := inner ℝ U V
  let gC : ℝ := inner ℝ V V
  have hangle₁ : gA * u * x - gA * u - gC * v * y + gC * y = 0 := by
    simp only [detCoeff, gram] at he₁
    dsimp [gA, gB, gC]
    linear_combination he₁
  have hangle₂ :
      -(2 * gA * u ^ 2 * x - 2 * gA * u ^ 2 - 2 * gA * u * x + 2 * gA * u +
        4 * gB * u * v * x - 4 * gB * u * v + gC * u * y +
        2 * gC * v ^ 2 * x - 2 * gC * v ^ 2 - gC * v * x +
        2 * gC * v * y + gC * v - gC * y) = 0 := by
    simp only [detCoeff, gram] at he₂
    dsimp [gA, gB, gC]
    linear_combination 4 * he₂
  have hangle₃ :
      -(2 * gA * u * x + gA * u * y - gA * u + 2 * gA * v * x ^ 2 -
        gA * v * x - 2 * gA * x ^ 2 + gA * x + 4 * gB * v * x * y -
        4 * gB * x * y + 2 * gC * v * y ^ 2 - 2 * gC * v * y -
        2 * gC * y ^ 2 + 2 * gC * y) = 0 := by
    simp only [detCoeff, gram] at he₃
    dsimp [gA, gB, gC]
    linear_combination 4 * he₃
  let H : ℝ :=
    2 * gA * u ^ 2 * x + 2 * gA * u ^ 2 * y - 2 * gA * u * x ^ 2 -
    gA * u * y - 2 * gA * v * x ^ 2 + gA * v * x +
    4 * gB * u * v * x + 4 * gB * u * v * y - 4 * gB * u * x * y -
    4 * gB * v * x * y - 2 * gC * u * y ^ 2 + gC * u * y +
    2 * gC * v ^ 2 * x + 2 * gC * v ^ 2 * y - gC * v * x -
    2 * gC * v * y ^ 2
  have hH : H = 0 :=
    p2_polynomial_certificate gA gB gC beta rho lam mu x y u v H
      hbeta hrho hlam hmu hbeta_lam hmu_rho
      hxyRay.1 hxyRay.2 huvRay.1 huvRay.2 hangle₁ hangle₂ hangle₃ rfl
  have hcenters :=
    p2_circumcenter_equations U V A K L O x y u v hKcoord hLcoord hO
  let p : ℝ := inner ℝ (O - A) U
  let q : ℝ := inner ℝ (O - A) V
  have hcenterK : 2 * (x * p + y * q) =
      gA * x ^ 2 + 2 * gB * x * y + gC * y ^ 2 := by
    dsimp [p, q, gA, gB, gC]
    linear_combination hcenters.1
  have hcenterL : 2 * (u * p + v * q) =
      gA * u ^ 2 + 2 * gB * u * v + gC * v ^ 2 := by
    dsimp [p, q, gA, gB, gC]
    linear_combination hcenters.2
  have hsyzygy :
      (x * v - y * u) * (gA - gC - 4 * p + 4 * q) = H :=
    p2_circumcenter_syzygy gA gB gC x y u v p q H
      hcenterK hcenterL rfl
  have hscalar : gA - gC - 4 * p + 4 * q = 0 :=
    p2_target_from_certificates gA gC beta lam x y u v p q H
      hbeta hxyRay.1 hxyRay.2 hH hv_pos hsyzygy
  have hmid := (scalar_target_iff_midpoint_equidistant U V A O).mp (by
    simpa [gA, gC, p, q] using hscalar)
  simpa [U, V] using hmid

end IMO2026P2

end S
