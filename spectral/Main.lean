import Mathlib

-- lemma 1.2 (unique extension of bounded densely defined operators)
-- is already in Mathlib as ContinuousLinearMap.extend

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]

/-- the domain of the Hilbert adjoint of a densely defined operator T : D(T) ⊆ H₁ → H₂ -/
def hilbertAdjointDomain (D : Submodule ℂ H₁) (T : D →ₗ[ℂ] H₂) : Set H₂ :=
 {y : H₂ | ∃ C : ℝ, ∀ x : D, ‖(inner (𝕜 := ℂ) (T x) y : ℂ)‖ ≤ C * ‖(x : H₁)‖}

/-- for y in the adjoint domain, the functional x ↦ ⟨Tx, y⟩ extends to a bounded linear functional on H₁ -/
noncomputable def adjointFunctional (D : Submodule ℂ H₁) (hD : Dense (D : Set H₁))
    (T : D →ₗ[ℂ] H₂) (y : H₂) (hy : y ∈ hilbertAdjointDomain D T) :
    H₁ →L[ℂ] ℂ := sorry

/-- the Hilbert adjoint T* : D(T*) ⊆ H₂ → H₁ -/
noncomputable def hilbertAdjoint (D : Submodule ℂ H₁) (hD : Dense (D : Set H₁))
    (T : D →ₗ[ℂ] H₂) (y : H₂) (hy : y ∈ hilbertAdjointDomain D T) : H₁ :=
  (InnerProductSpace.toDual ℂ H₁).symm (adjointFunctional D hD T y hy)
