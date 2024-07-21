import Mathlib.Topology.MetricSpace.Basic
import Verbose.Italian.All

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

notation3:50 f:80 " è continua in " x₀ => continuous_function_at f x₀
notation3:50 u:80 " tende a " l => sequence_tendsto u l

def increasing (u : ℕ → ℝ) := ∀ n m, n ≤ m → u n ≤ u m

notation3 u " è crescente" => increasing u

def is_supremum (M : ℝ) (u : ℕ → ℝ) :=
(∀ n, u n ≤ M) ∧ ∀ ε > 0, ∃ n₀, u n₀ ≥ M - ε

notation3 M " è un estremo superiore di " u => is_supremum M u

configureUnfoldableDefs continuous_function_at sequence_tendsto increasing is_supremum

section Subset
variable {α : Type*}

/- The Mathlib definition of `Set.Subset` uses a strict-implicit
argument which confuses Verbose Lean. So let us replace it. -/

protected def Verbose.Italian.Subset (s₁ s₂ : Set α) :=
  ∀ a, a ∈ s₁ → a ∈ s₂

instance (priority := high) Verbose.Italian.hasSubset : HasSubset (Set α) :=
  ⟨Verbose.Italian.Subset⟩

end Subset

open Verbose.Italian

configureAnonymousFactSplittingLemmas le_le_of_abs_le le_le_of_max_le

configureAnonymousGoalSplittingLemmas LogicIntros AbsIntros Set.Subset.antisymm

useDefaultDataProviders

useDefaultSuggestionProviders
