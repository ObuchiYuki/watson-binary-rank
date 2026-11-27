import WatsonBinaryRank.CodeRule

/-!
# Kernels of parity-check matrices have the face property

If `H` is an `m × k` matrix over `F₂` and the `m × m` submatrix on the columns `Z` is invertible,
then `ker H` meets every face fixing the coordinates outside `Z` in exactly one point.
-/

namespace WatsonBinaryRank

open Matrix

variable {k m : ℕ}

/-- The columns of `H` indexed by `Z` (listed by `emb`). -/
def subCols (H : Matrix (Fin m) (Fin k) (ZMod 2)) (Z : Finset (Fin k)) (emb : Fin m ≃ Z) :
    Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of fun r j => H r (emb j : Fin k)

/-- The kernel of `H`. -/
def kerSet (H : Matrix (Fin m) (Fin k) (ZMod 2)) : Set (Fin k → ZMod 2) :=
  {y | H *ᵥ y = 0}

open Classical in
/-- Zero out the coordinates in `Z`. -/
noncomputable def outPart (Z : Finset (Fin k)) (y : Fin k → ZMod 2) : Fin k → ZMod 2 :=
  fun i => if i ∈ Z then 0 else y i

open Classical in
lemma mulVec_split (H : Matrix (Fin m) (Fin k) (ZMod 2)) (Z : Finset (Fin k)) (emb : Fin m ≃ Z)
    (y : Fin k → ZMod 2) :
    H *ᵥ y = H *ᵥ outPart Z y + subCols H Z emb *ᵥ (fun j => y (emb j)) := by
  funext r
  simp only [Pi.add_apply, mulVec, dotProduct, subCols, of_apply, outPart]
  have h1 : ∑ i, H r i * y i = ∑ i, (H r i * (if i ∈ Z then 0 else y i)) +
      ∑ i, (if i ∈ Z then H r i * y i else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [h1]
  congr 1
  rw [← Finset.sum_filter]
  have : (Finset.univ.filter (· ∈ Z)) = Z := by ext; simp
  rw [this, ← Finset.sum_coe_sort Z]
  exact (Equiv.sum_comp emb (fun j : Z => H r j * y j)).symm

open Classical in
theorem faceProp_kerSet (H : Matrix (Fin m) (Fin k) (ZMod 2)) (Z : Finset (Fin k))
    (emb : Fin m ≃ Z) (hdet : (subCols H Z emb).det ≠ 0) :
    FaceProp (kerSet H) Z := by
  set A := subCols H Z emb
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  intro y
  let w := outPart Z y
  let u : Fin m → ZMod 2 := A⁻¹ *ᵥ (-(H *ᵥ w))
  let y' : Fin k → ZMod 2 := fun i => if h : i ∈ Z then u (emb.symm ⟨i, h⟩) else y i
  have hout' : outPart Z y' = w := by
    funext i; simp only [outPart, w, y']; split_ifs <;> simp_all
  have hin' : (fun j => y' (emb j)) = u := by
    funext j; simp [y']
  refine ⟨y', ⟨?_, ?_⟩, ?_⟩
  · show H *ᵥ y' = 0
    rw [mulVec_split H Z emb y', hout', hin']
    show H *ᵥ w + A *ᵥ (A⁻¹ *ᵥ (-(H *ᵥ w))) = 0
    rw [mulVec_mulVec, mul_nonsing_inv _ hA, one_mulVec]
    exact add_neg_cancel _
  · intro i hi; simp [y', hi]
  · rintro y'' ⟨hker, hagree⟩
    have hw'' : outPart Z y'' = w := by
      funext i; simp only [outPart, w]; split_ifs with h
      · rfl
      · exact hagree i h
    have hA'' : A *ᵥ (fun j => y'' (emb j)) = -(H *ᵥ w) := by
      have := mulVec_split H Z emb y''
      rw [hker, hw''] at this
      exact (neg_eq_of_add_eq_zero_right this.symm).symm
    have hu'' : (fun j => y'' (emb j)) = u := by
      show _ = A⁻¹ *ᵥ (-(H *ᵥ w))
      rw [← hA'', mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec]
    funext i
    by_cases h : i ∈ Z
    · have := congrFun hu'' (emb.symm ⟨i, h⟩)
      simp only [Equiv.apply_symm_apply] at this
      simp [y', h, ← this]
    · simp [y', h, hagree i h]

end WatsonBinaryRank
