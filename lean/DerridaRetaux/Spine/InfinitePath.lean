import DerridaRetaux.Spine.Coupling
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.MeasureComp

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DerridaRetaux

noncomputable section

/-- The finite history type used by the Ionescu--Tulcea theorem. -/
abbrev SpineHistory (n : ℕ) := (i : Finset.Iic n) → ℕ

/-- Reindex a finite spine path by the closed natural interval. -/
def spineToHistory (n : ℕ) (u : Fin (n + 1) → ℕ) : SpineHistory n :=
  fun i ↦ u ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩

/-- Inverse reindexing of a finite spine history. -/
def spineFromHistory (n : ℕ) (u : SpineHistory n) : Fin (n + 1) → ℕ :=
  fun i ↦ u ⟨i.1, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩

@[simp] theorem spineFromHistory_toHistory (n : ℕ) (u : Fin (n + 1) → ℕ) :
    spineFromHistory n (spineToHistory n u) = u := rfl

@[simp] theorem spineToHistory_fromHistory (n : ℕ) (u : SpineHistory n) :
    spineToHistory n (spineFromHistory n u) = u := rfl

/-- The last value of a history. -/
def spineHistoryLast (n : ℕ) (u : SpineHistory n) : ℕ :=
  u ⟨n, Finset.mem_Iic.mpr le_rfl⟩

/-- The next-state distribution depends only on the last state, not the earlier history. -/
def spineHistoryKernel (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    Kernel (SpineHistory n) ℕ :=
  Kernel.ofFunOfCountable fun u ↦ (spineKernel m data n (spineHistoryLast n u)).toMeasure

instance spineHistoryKernel_isMarkov (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    IsMarkovKernel (spineHistoryKernel m data n) := by
  constructor
  intro u
  change IsProbabilityMeasure (spineKernel m data n (spineHistoryLast n u)).toMeasure
  infer_instance

/-- The actual finite path distribution, in the history indexing convention. -/
def spineHistoryPMF (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    PMF (SpineHistory n) := (spinePathPMF m data n).map (spineToHistory n)

/-- Probability measure on a single space of infinite trajectories. -/
def spineInfinitePathMeasure (m : ℕ) (data : ProfileInitialData m) : Measure (ℕ → ℕ) :=
  Kernel.traj (X := fun _ ↦ ℕ) (spineHistoryKernel m data) 0 ∘ₘ
    (spineHistoryPMF m data 0).toMeasure

instance spineInfinitePathMeasure_isProbability (m : ℕ) (data : ProfileInitialData m) :
    IsProbabilityMeasure (spineInfinitePathMeasure m data) := by
  unfold spineInfinitePathMeasure
  infer_instance

private theorem pmf_kernel_comp
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α]
    (p : PMF α) (q : α → PMF β) :
    (Kernel.ofFunOfCountable fun a ↦ (q a).toMeasure) ∘ₘ p.toMeasure =
      (p.bind q).toMeasure := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), PMF.toMeasure_bind_apply _ _ _ hs]
  simp only [lintegral_countable', PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  congr 1
  funext a
  exact mul_comm _ _

private def spineAppendHistory (n : ℕ) (u : SpineHistory n) (k : ℕ) :
    SpineHistory (n + 1) := spineToHistory (n + 1) (Fin.snoc (spineFromHistory n u) k)

private theorem spine_step_kernel (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    (Kernel.id ×ₖ ((spineHistoryKernel m data n).map
      (MeasurableEquiv.piSingleton (X := fun _ ↦ ℕ) n))).map
      (_root_.IicProdIoc (X := fun _ ↦ ℕ) n (n + 1)) =
    Kernel.ofFunOfCountable (fun u : SpineHistory n ↦
      ((spineKernel m data n (spineHistoryLast n u)).map
        (spineAppendHistory n u)).toMeasure) := by
  ext u : 1
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply,
    Kernel.map_apply _ (by fun_prop), Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  change ((spineKernel m data n (spineHistoryLast n u)).toMeasure).map _ = _
  rw [PMF.toMeasure_map _ _ (by exact measurable_of_countable _)]
  congr 2
  funext k i
  dsimp [spineAppendHistory, spineToHistory, spineFromHistory,
    _root_.IicProdIoc, MeasurableEquiv.piSingleton]
  split_ifs with hi
  · simp [Fin.snoc, Nat.lt_succ_of_le hi, spineFromHistory]
  · have hnot : ¬ i.1 < n + 1 := by omega
    simp [Fin.snoc, hnot]

private theorem spineHistoryPMF_succ (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    spineHistoryPMF m data (n + 1) =
      (spineHistoryPMF m data n).bind (fun u ↦
        (spineKernel m data n (spineHistoryLast n u)).map (spineAppendHistory n u)) := by
  simp only [spineHistoryPMF, spinePathPMF, PMF.map_bind, PMF.bind_map, PMF.map_comp]
  rfl

/-- Every finite restriction of the infinite measure is the previously constructed path law. -/
theorem spineInfinitePathMeasure_history (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    (spineInfinitePathMeasure m data).map (Preorder.frestrictLe n) =
      (spineHistoryPMF m data n).toMeasure := by
  unfold spineInfinitePathMeasure
  rw [Measure.map_comp _ _ (by fun_prop), Kernel.traj_map_frestrictLe]
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Kernel.partialTraj_succ_of_le (Nat.zero_le n),
        Kernel.map_comp, ← Measure.comp_assoc, spine_step_kernel, ih,
        pmf_kernel_comp, ← spineHistoryPMF_succ]

/-- Literal finite-coordinate law on the common infinite path space. Together with the
recursive definition of `spinePathPMF`, this specifies the Markov chain at all horizons. -/
theorem spineInfinitePathMeasure_finiteLaw
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    (spineInfinitePathMeasure m data).map (fun w (i : Fin (n + 1)) ↦ w i) =
      (spinePathPMF m data n).toMeasure := by
  have h := congrArg (fun μ : Measure (SpineHistory n) ↦
    μ.map (spineFromHistory n)) (spineInfinitePathMeasure_history m data n)
  dsimp only at h
  rw [Measure.map_map (measurable_of_countable _) (by fun_prop),
    spineHistoryPMF, ← PMF.toMeasure_map _ _ (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at h
  change (spineInfinitePathMeasure m data).map (fun w (i : Fin (n + 1)) ↦ w i) =
    (spinePathPMF m data n).toMeasure.map id at h
  simpa only [Measure.map_id] using h

/-- Every coordinate has the required cubic-weighted marginal on the same probability space. -/
theorem spineInfinitePathMeasure_marginal
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    (spineInfinitePathMeasure m data).map (fun w ↦ w n) =
      (spineMarginalPMF m data n).toMeasure := by
  have h := congrArg (fun μ : Measure (Fin (n + 1) → ℕ) ↦
    μ.map finPathTerminal) (spineInfinitePathMeasure_finiteLaw m data n)
  dsimp only at h
  rw [Measure.map_map (measurable_of_countable _) (by fun_prop),
    PMF.toMeasure_map _ _ (measurable_of_countable _), spinePathPMF_terminal_marginal] at h
  exact h

/-- The joint law of the full past and the next state factors through the current state.
This is the Markov transition identity, including histories of probability zero. -/
theorem spineInfinitePathMeasure_markov
    (m : ℕ) (data : ProfileInitialData m) (n : ℕ) :
    (spineInfinitePathMeasure m data).map
        (fun w ↦ ((fun i : Fin (n + 1) ↦ w i), w (n + 1))) =
      ((spinePathPMF m data n).bind (fun u ↦
        (spineKernel m data n (finPathTerminal u)).map (fun k ↦ (u, k)))).toMeasure := by
  let split : (Fin (n + 2) → ℕ) → (Fin (n + 1) → ℕ) × ℕ :=
    fun u ↦ ((fun i ↦ u i.castSucc), u (Fin.last (n + 1)))
  have h := congrArg (fun μ : Measure (Fin (n + 2) → ℕ) ↦ μ.map split)
    (spineInfinitePathMeasure_finiteLaw m data (n + 1))
  dsimp only at h
  rw [Measure.map_map (measurable_of_countable _) (by fun_prop),
    PMF.toMeasure_map _ _ (measurable_of_countable _)] at h
  simpa [split, spinePathPMF, PMF.map_bind, PMF.map_comp, Function.comp_def] using h

namespace FixedArity

/-- The process-existence clause of `lem:spine`: a probability measure on infinite
trajectories, all finite path laws, the required marginals, and the Markov transition law.
The existing `cubicWeightedChain` supplies the exact increment and tail estimates for these laws. -/
theorem cubicWeightedInfiniteChain (m : ℕ) (data : ProfileInitialData m) :
    ∃ μ : Measure (ℕ → ℕ), IsProbabilityMeasure μ ∧
      (∀ n : ℕ, μ.map (fun w (i : Fin (n + 1)) ↦ w i) =
        (spinePathPMF m data n).toMeasure) ∧
      (∀ n : ℕ, μ.map (fun w ↦ w n) = (spineMarginalPMF m data n).toMeasure) ∧
      (∀ n : ℕ, μ.map (fun w ↦ ((fun i : Fin (n + 1) ↦ w i), w (n + 1))) =
        ((spinePathPMF m data n).bind (fun u ↦
          (spineKernel m data n (finPathTerminal u)).map (fun k ↦ (u, k)))).toMeasure) := by
  exact ⟨spineInfinitePathMeasure m data, inferInstance,
    spineInfinitePathMeasure_finiteLaw m data, spineInfinitePathMeasure_marginal m data,
    spineInfinitePathMeasure_markov m data⟩

end FixedArity

end
end DerridaRetaux
