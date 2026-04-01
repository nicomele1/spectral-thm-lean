import Mathlib

-- Lemma 1.2 (unique extension of bounded densely defined operators)
-- is already in Mathlib as ContinuousLinearMap.extend

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

/-- The domain of the Hilbert adjoint of a densely defined operator T : D(T) ⊆ H₁ → H₂ -/
def hilbertAdjointDomain (D : Submodule ℂ H₁) (T : D →ₗ[ℂ] H₂) : Set H₂ :=
  {y : H₂ | ∃ C : ℝ, ∀ x : D, ‖(inner (𝕜 := ℂ) y (T x) : ℂ)‖ ≤ C * ‖(x : H₁)‖}

/-- For y in the adjoint domain, the functional x ↦ ⟨y, Tx⟩ extends to a bounded
    linear functional on H₁ -/
noncomputable def adjointFunctional (D : Submodule ℂ H₁) (hD : Dense (D : Set H₁))
    (T : D →ₗ[ℂ] H₂) (y : H₂) (hy : y ∈ hilbertAdjointDomain D T) :
    H₁ →L[ℂ] ℂ :=
  let C := Classical.choose hy
  let hC := Classical.choose_spec hy
  let φ₀ : D →ₗ[ℂ] ℂ := {
    toFun := fun x => inner (𝕜 := ℂ) y (T x)
    map_add' := fun x z => by simp [map_add]
    map_smul' := fun m x => by
      simp only [RingHom.id_apply, map_smul, inner_smul_right, smul_eq_mul]
  }
  let φ : D →L[ℂ] ℂ := φ₀.mkContinuous C (fun x => hC x)
  haveI : IsUniformAddGroup (↥D) := SeminormedAddCommGroup.to_isUniformAddGroup
  φ.extend D.subtypeL
/-- The Hilbert adjoint T* : D(T*) ⊆ H₂ → H₁ -/
noncomputable def hilbertAdjoint (D : Submodule ℂ H₁) (hD : Dense (D : Set H₁))
    (T : D →ₗ[ℂ] H₂) (y : H₂) (hy : y ∈ hilbertAdjointDomain D T) : H₁ :=
  (InnerProductSpace.toDual ℂ H₁).symm (adjointFunctional D hD T y hy)
