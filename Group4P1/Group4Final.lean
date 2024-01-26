--小组成员：胥天乐，闵圣骐，彭煜杰，戴其铭
import Init.Prelude
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Pointwise
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix



namespace Matrix
noncomputable section
variable {n : Type*} [DecidableEq n] [Fintype n]

set_option maxHeartbeats 20000000

-- The BFGS update function could be defined in terms of these operations.
def Bsucc (B: Matrix n n ℝ  )(s y : Matrix n (Fin 1) ℝ  ): Matrix n n ℝ   :=
  B - (1/(sᵀ  * B * s) 0 0) • (B * s * sᵀ * B) + (1/(yᵀ * s) 0 0) • (y * yᵀ)

def norm2 (v : Matrix n (Fin 1) ℝ ) : ℝ  :=
  (vᵀ * v) 0 0


-- Theorems would be stated using these definitions.
theorem trace_BFGS_update {B : Matrix n n ℝ } {s y : Matrix n (Fin 1) ℝ } (h : Bᵀ = B):
    trace (Bsucc B s y) = trace (B) - (norm2 (B * s)) * (1 / (sᵀ * B * s) 0 0)
    + (norm2 y) * (1/(yᵀ * s) 0 0) := by
      unfold Bsucc
      rw[trace_add,trace_sub,trace_smul,trace_smul]
      have h': (1 / (sᵀ * B * s) 0 0) • trace (B * s * sᵀ * B)
      = (norm2 (B * s)) * (1 / (sᵀ * B * s) 0 0) := by
        have : trace (B * s * sᵀ * B) = norm2 (B*s) :=by
          rw[trace_mul_comm,← Matrix.mul_assoc,trace_mul_comm,← Matrix.mul_assoc]
          have : sᵀ * B = (B * s)ᵀ :=by rw[Matrix.transpose_mul,h]
          rw[this]
          unfold trace;unfold norm2;simp
        rw[this]
        simp;rw[mul_comm]
      have g': (1 / (yᵀ * s) 0 0) • trace (y * yᵀ) = (norm2 y) * (1 / (yᵀ * s) 0 0) := by
        have : trace (y * yᵀ) = norm2 y:=by
          rw[trace_mul_comm]
          unfold trace;unfold norm2;simp
        rw[this]
        simp;rw[mul_comm]
      rw[h'];rw[g']

--   this is the S-M-W formula
theorem SMW (u v : Matrix n (Fin 1) ℝ) (h : det (1 + vᵀ * u) ≠ 0):
    (1 + u * vᵀ)⁻¹ = 1 - (u * (1 + vᵀ * u)⁻¹ * vᵀ) := by
      have h' : (1 - (u * (1 + vᵀ * u)⁻¹ * vᵀ)) * (1 + u * vᵀ) = 1 := by
        rw[sub_mul];rw[one_mul]
        have h'' : u * (1 + vᵀ * u)⁻¹ * vᵀ * (1 + u * vᵀ) = u * vᵀ := by
          rw[mul_add, ← Matrix.mul_assoc, mul_one]
          rw[Matrix.mul_assoc (u * (1 + vᵀ * u)⁻¹ * vᵀ) u vᵀ]
          rw[Matrix.mul_assoc (u * (1 + vᵀ * u)⁻¹) vᵀ (u * vᵀ)];rw[← Matrix.mul_assoc vᵀ u vᵀ]
          rw[← Matrix.mul_add];nth_rw 2 [← Matrix.one_mul vᵀ]
          rw[← Matrix.add_mul, ← Matrix.mul_assoc]
          have : (1 + vᵀ * u)⁻¹ * (1 + vᵀ * u) = 1 := by
            rw[Matrix.nonsing_inv_mul];unfold IsUnit
            simp;by_contra h';apply h
            rw[Matrix.det_fin_one];exact h'
          rw[Matrix.mul_assoc, Matrix.mul_assoc]
          rw[← Matrix.mul_assoc (1 + vᵀ * u)⁻¹ (1 + vᵀ * u) vᵀ];rw[this, Matrix.one_mul]
        rw[h''];rw[← add_sub, sub_self, add_zero]
      apply Matrix.inv_eq_left_inv;exact h'

theorem lemma1 (u v : Matrix n (Fin 1) ℝ) :
    det (1 + u * vᵀ) = det (1 + vᵀ * u) := by
      simp
      let A := Matrix.fromBlocks 1 (-u) vᵀ 1
      let T1 := Matrix.fromBlocks (1:Matrix n n ℝ) u 0 (1:Matrix (Fin 1) (Fin 1) ℝ)
      let AT1 :=  A * T1
      have : AT1 = fromBlocks 1 0 vᵀ (1  + vᵀ * u) := by
        simp;rw[Matrix.fromBlocks_multiply]
        apply Matrix.ext_iff_blocks.2
        constructor
        · simp
        · simp;rw[add_comm]
      have : det AT1 = det (1 + vᵀ * u) := by
        rw[this];rw[Matrix.det_fromBlocks_zero₁₂, det_one]
        ring
      symm
      have : det AT1 = 1 + (vᵀ * u) 0 0 := by
        rw[this];simp
      rw[← this]
      have : det AT1 =  det A := by
        simp
      rw[this]
      let T2 := fromBlocks (1 : Matrix n n ℝ) u 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)
      let AT2 := T2 * A
      have : AT2 = fromBlocks (1 + u * vᵀ) 0 vᵀ 1 := by
        simp;rw[Matrix.fromBlocks_multiply]
        apply Matrix.ext_iff_blocks.2
        constructor
        · simp
        · simp
      have : det AT2 = det (1 + u * vᵀ) := by
        rw[this];rw[Matrix.det_fromBlocks_zero₁₂, det_one]
        ring
      symm;rw[← this]
      have : det AT2 = det A := by
        simp
      rw[this]



--  det (1 + u * vᵀ + x * yᵀ) = (1 + vᵀ * u)(1 + yᵀ * x) - (vᵀ * x) * (yᵀ * u)
theorem lemma2 (u v x y : Matrix n (Fin 1) ℝ) (h : det (1 + vᵀ * u) ≠ 0) :
    det (1 + u * vᵀ + x * yᵀ) = (((1 : Matrix (Fin 1) (Fin 1) ℝ ) + vᵀ * u) 0 0)
    * (((1 : Matrix (Fin 1) (Fin 1) ℝ ) + yᵀ * x) 0 0) - ((vᵀ * x) 0 0) * ((yᵀ * u) 0 0) := by
      have h2 : 1 + u * vᵀ + x * yᵀ = (1 + u * vᵀ) * (1 + (1 + u * vᵀ)⁻¹ * (x * yᵀ)) := by
        symm
        rw [mul_add, ← mul_assoc]
        rw[Matrix.mul_nonsing_inv];rw[mul_one, one_mul]
        unfold IsUnit;simp;by_contra h';apply h;rw[← lemma1];exact h'
      have h3 : det (1 + u * vᵀ + x * yᵀ)
                = det (1 + vᵀ * u) * det (1 + yᵀ * x - yᵀ * u * (1 + vᵀ * u)⁻¹ * vᵀ * x) := by
        calc
          det (1 + u * vᵀ + x * yᵀ) = det ((1 + u * vᵀ) * (1 + (1 + u * vᵀ)⁻¹ * (x * yᵀ))) := by
            rw[h2]
          _ = det (1 + u * vᵀ) * det (1 + (1 + u * vᵀ)⁻¹ * (x * yᵀ)) := by
            apply det_mul (1 + u * vᵀ) (1 + (1 + u * vᵀ)⁻¹ * (x * yᵀ))
          _ = det (1 + vᵀ * u) * det (1 + (1 + u * vᵀ)⁻¹ * x * yᵀ) := by
            rw[lemma1 u v]; rw[← Matrix.mul_assoc]
          _ = det (1 + vᵀ * u) * det (1 + yᵀ * (1 + u * vᵀ)⁻¹ * x) := by
            rw[lemma1 ((1 + u * vᵀ)⁻¹ * x) y, ← Matrix.mul_assoc]
          _ = det (1 + vᵀ * u) * det (1 + yᵀ * (1 - (u * (1 + vᵀ * u)⁻¹ * vᵀ)) * x) := by
            rw[SMW u v h]
          _ = det (1 + vᵀ * u) * det (1 + yᵀ * x - yᵀ * u * (1 + vᵀ * u)⁻¹ * vᵀ * x) :=by
            rw[Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, add_sub]
            rw[← Matrix.mul_assoc,← Matrix.mul_assoc]
      rw[h3];rw[Matrix.det_fin_one, Matrix.det_fin_one, Matrix.sub_apply, mul_sub]
      have : ((1 : Matrix (Fin 1) (Fin 1) ℝ ) + vᵀ * u) 0 0
            * (yᵀ * u * ((1 : Matrix (Fin 1) (Fin 1) ℝ ) + vᵀ * u)⁻¹ * vᵀ * x) 0 0
            = ((vᵀ * x) 0 0) * ((yᵀ * u) 0 0) :=by
        rw[← Matrix.det_fin_one ((1 : Matrix (Fin 1) (Fin 1) ℝ ) + vᵀ * u)];
        rw[← Matrix.det_fin_one (yᵀ * u * ((1 : Matrix (Fin 1) (Fin 1) ℝ ) + vᵀ * u)⁻¹ * vᵀ * x)]
        rw[Matrix.mul_assoc];rw[Matrix.det_mul];rw[Matrix.det_mul];rw[← mul_assoc, ← mul_assoc]
        rw[mul_comm (det ((1 : Matrix (Fin 1) (Fin 1) ℝ ) + vᵀ * u)) (det (yᵀ * u))]
        rw[mul_assoc (det (yᵀ * u)) (det (1 + vᵀ * u)) (det (1 + vᵀ * u)⁻¹)]
        rw[← Matrix.det_mul];rw[Matrix.mul_nonsing_inv];rw[Matrix.det_one]
        rw[mul_one, Matrix.det_fin_one, Matrix.det_fin_one];ring
        unfold IsUnit;simp;by_contra h';apply h;rw[Matrix.det_fin_one];exact h'
      rw[this]


variable(zero':(Fin 1))
def f (v : Matrix n (Fin 1) ℝ)(x : n) := v x 0
variable (x : Matrix n (Fin 1) ℝ)
#check f x
theorem Pos1 {B : Matrix n n ℝ } (h : PosDef B):
    ∀ x : Matrix n (Fin 1) ℝ, x ≠ 0 → ((xᵀ * B * x) 0 0) > 0 :=by
      rcases h with ⟨h1,h2⟩
      intro x xnozero
      specialize h2 (f x)
      have : f x ≠ 0 :=by
        by_contra h
        apply xnozero
        apply Matrix.ext_iff.mp;unfold f at h;intro i j;simp
        have g: (fun x_1 => x x_1 0) i = 0 :=by
          rw[h];simp
        simp at g
        have : j = 0 :=by
          apply Fin.fin_one_eq_zero
        rw[this]
        exact g
      have h': 0 < star (f x) ⬝ᵥ mulVec B (f x) :=by apply h2 this
      have h'' : ((xᵀ * B * x) 0 0) = star (f x) ⬝ᵥ mulVec B (f x) :=by
        simp;unfold dotProduct;sorry
      sorry

theorem det_BFGS_update {B : Matrix n n ℝ } {s y : Matrix n (Fin 1) ℝ }
    (h1 : PosDef B)(h2 : (yᵀ * s) 0 0 > (0:ℝ)):
    det (Bsucc B s y) = (det B) * ((yᵀ * s) 0 0) / ((sᵀ * B * s) 0 0):= by
      have Bsymm : Bᵀ = B :=by apply Matrix.PosDef.isHermitian;apply h1
      have g1 : ∀ x : Matrix n (Fin 1) ℝ, x ≠ 0 → ((xᵀ * B * x) 0 0) > 0 :=by apply Pos1 h1
      have Bdetpos : 0 < det B := by exact Matrix.PosDef.det_pos h1
      have detB_unit : IsUnit (det B) := by unfold IsUnit;simp;by_contra h';linarith [Bdetpos]
      have Binv : Invertible B := by apply Matrix.invertibleOfIsUnitDet B detB_unit
      have B_inv_symm : B⁻¹ᵀ = B⁻¹ := by
        have : B⁻¹ = ⅟B := by
          simp
        rw[this];rw[Matrix.transpose_invOf]
        simp;rw[Bsymm]
      have g : (yᵀ * s) 0 0 = (sᵀ * y) 0 0 :=by
        rw[← Matrix.det_fin_one (yᵀ * s)];rw[← Matrix.det_fin_one (sᵀ * y)]
        have : (yᵀ * s)ᵀ = sᵀ * y :=by rw[Matrix.transpose_mul];simp
        rw[← this, Matrix.det_transpose]
      have h6 : 0 < (yᵀ * B⁻¹ * y) 0 0 := by
        have : yᵀ * B⁻¹ * y = (B⁻¹ * y)ᵀ * B * (B⁻¹ * y) := by
          rw[Matrix.transpose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (yᵀ * B⁻¹ᵀ)]
          rw[Matrix.mul_nonsing_inv]
          rw[Matrix.mul_one, B_inv_symm];exact detB_unit
        rw[this]
        specialize g1 (B⁻¹ * y)
        have g2 : y ≠ 0 :=by
          rw[g] at h2
          by_contra g3;rw[g3] at h2
          rw[Matrix.mul_zero] at h2;simp at h2
        have : B⁻¹ * y ≠ 0 := by
          by_contra g3;apply g2
          calc
            y = B * B⁻¹ * y := by
              rw[Matrix.mul_nonsing_inv, Matrix.one_mul]
              apply detB_unit
            _ = B * (0 : Matrix n (Fin 1) ℝ) := by
              rw[Matrix.mul_assoc,g3]
            _ = 0 := by
              rw[Matrix.mul_zero]
        apply g1 this
      let u := (1 / (sᵀ * y) 0 0) • (B⁻¹ * y)
      let x := (1 / (sᵀ * B * s) 0 0) • s
      let z := - (B * s)
      have h' : det (1 + yᵀ * u) ≠ 0 := by
        rw[Matrix.det_fin_one]
        have : 1 + yᵀ * u = 1 + ((1 / (sᵀ * y) 0 0) • (yᵀ * B⁻¹ * y)) := by
          calc
            1 + yᵀ * u = 1 + yᵀ * (1 / (sᵀ * y) 0 0) • (B⁻¹ * y) := by rfl
            _ = 1 + (1 / (sᵀ * y) 0 0) • (yᵀ * (B⁻¹ * y)) := by
              rw[mul_smul yᵀ (1 / (sᵀ * y) 0 0) (B⁻¹ * y)]
            _ = 1 + (1 / (sᵀ * y) 0 0) • (yᵀ * B⁻¹ * y) := by rw[← Matrix.mul_assoc]
        rw [this]
        simp
        rw[← g]
        have : 0 ≤  ((yᵀ * s) 0 0)⁻¹ * (yᵀ * B⁻¹ * y) 0 0 :=by
          rw[← mul_zero 0]
          apply mul_le_mul;apply le_of_lt;apply inv_pos.mpr;exact h2
          apply le_of_lt;exact h6;linarith;apply le_of_lt;apply inv_pos.mpr;exact h2
        push_neg;apply ne_iff_lt_or_gt.mpr;right
        linarith
      have eq1 : (det B) * det (1 + u * yᵀ + x * zᵀ)
        = (det B) * ((((1 : Matrix (Fin 1) (Fin 1) ℝ ) + yᵀ * u) 0 0)
        * (((1 : Matrix (Fin 1) (Fin 1) ℝ ) + zᵀ * x) 0 0) - ((yᵀ * x) 0 0) * ((zᵀ * u) 0 0)) := by
          rw [lemma2 u y x z h']
      have eq2 : (det B) * det (1 + u * yᵀ + x * zᵀ) = det (Bsucc B s y) := by
        rw[← det_mul]
        have : B * (1 + u * yᵀ + x * zᵀ) = Bsucc B s y := by
          simp;rw[mul_add,mul_add]
          unfold Bsucc;simp
          rw[← Matrix.mul_assoc B (B⁻¹ * y) yᵀ,← Matrix.mul_assoc,Matrix.mul_nonsing_inv,← g]
          simp
          rw[Bsymm, add_assoc];rw[add_comm,add_assoc,neg_add_eq_sub,← add_sub_assoc,add_comm]
          have : B * (s * (sᵀ * B)) = B * s * sᵀ * B := by
            symm;rw[Matrix.mul_assoc,Matrix.mul_assoc]
          rw[this,add_sub_right_comm]
          apply detB_unit
        rw[this]
      have eq3 :
        (((1 : Matrix (Fin 1) (Fin 1) ℝ ) + yᵀ * u) 0 0) * (((1 : Matrix (Fin 1) (Fin 1) ℝ ) + zᵀ * x) 0 0)
        - ((yᵀ * x) 0 0) * ((zᵀ * u) 0 0)
        = ((yᵀ * s) 0 0) / ((sᵀ * B * s) 0 0) := by
        have : (((1 : Matrix (Fin 1) (Fin 1) ℝ ) + zᵀ * x) 0 0) = 0 :=by
          simp;rw[Bsymm]
          have g2 : s ≠ 0 :=by
            by_contra g3;rw[g3] at h2;rw[Matrix.mul_zero] at h2;simp at h2
          specialize g1 s g2
          rw[inv_mul_cancel]<;>linarith
        rw[this];rw[mul_zero]
        simp
        have : ((sᵀ * y) 0 0)⁻¹ * (sᵀ * Bᵀ * (B⁻¹ * y)) 0 0 = 1 :=by
          rw[Bsymm];rw[Matrix.mul_assoc sᵀ B (B⁻¹ * y)];rw[← Matrix.mul_assoc B B⁻¹ y]
          rw[Matrix.mul_nonsing_inv, Matrix.one_mul,inv_mul_cancel]
          rw[← g];linarith;exact detB_unit
        rw[this, mul_one]
        field_simp
      rw[← eq2, eq1, eq3]; ring
