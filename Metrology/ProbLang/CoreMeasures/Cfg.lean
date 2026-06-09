module

public import Metrology.ProbLang.CoreMeasures.Exp
public import Metrology.ProbLang.CoreMeasures.Val
public import Metrology.ProbLang.CoreMeasures.State

@[expose] public section

noncomputable section
open Classical MeasureTheory

namespace ProbLang

instance instMeasurableSpaceTape : MeasurableSpace Tape := ⊤

instance instMeasurableSingletonClassTape : MeasurableSingletonClass Tape :=
  ⟨fun _ => trivial⟩

instance instMeasurableSpaceState {α : Type _} [MeasurableSpace α] :
    MeasurableSpace (State α) :=
  MeasurableSpace.comap (fun σ : State α => (σ.heap, σ.tapes)) inferInstance

@[fun_prop]
theorem State.measurable_heap {α : Type _} [MeasurableSpace α] :
    Measurable (fun σ : State α => σ.heap) :=
  measurable_fst.comp (Measurable.of_comap_le le_rfl)

@[fun_prop]
theorem State.measurable_tapes {α : Type _} [MeasurableSpace α] :
    Measurable (fun σ : State α => σ.tapes) :=
  measurable_snd.comp (Measurable.of_comap_le le_rfl)

theorem State.measurable_iff {X α : Type _} [MeasurableSpace X] [MeasurableSpace α]
    {f : X → State α} :
    Measurable f
      ↔ Measurable (fun x => (f x).heap) ∧ Measurable (fun x => (f x).tapes) :=
  ⟨fun hf => ⟨State.measurable_heap.comp hf, State.measurable_tapes.comp hf⟩,
   fun ⟨h₁, h₂⟩ =>
     (measurable_comap_iff (g := fun σ : State α => (σ.heap, σ.tapes))).mpr (h₁.prodMk h₂)⟩

@[fun_prop]
theorem State.measurable_mk {α : Type _} [MeasurableSpace α] :
    Measurable (fun (p : LocHeap (Val α) × LocHeap Tape) => State.mk p.1 p.2) :=
  State.measurable_iff.mpr ⟨measurable_fst, measurable_snd⟩

/-- Stamping helper: `State.mk` parameterized over `γ`. Given measurable
heap and tape extractors, the resulting `State` is measurable. Concise alternative
to `rw [State.measurable_iff]; refine ⟨he, ht⟩`. -/
@[fun_prop]
theorem State.measurable_mk_param {α γ : Type _} [MeasurableSpace α] [MeasurableSpace γ]
    {fh : γ → LocHeap (Val α)} (hh : Measurable fh)
    {ft : γ → LocHeap Tape} (ht : Measurable ft) :
    Measurable (fun q : γ => State.mk (fh q) (ft q)) :=
  State.measurable_iff.mpr ⟨hh, ht⟩

instance instMeasurableSpaceCfg {α : Type _} [MeasurableSpace α] :
    MeasurableSpace (Cfg α) :=
  MeasurableSpace.comap (fun c : Cfg α => (c.expr, c.state)) inferInstance

@[fun_prop]
theorem Cfg.measurable_expr {α : Type _} [MeasurableSpace α] :
    Measurable (fun c : Cfg α => c.expr) :=
  measurable_fst.comp (Measurable.of_comap_le le_rfl)

@[fun_prop]
theorem Cfg.measurable_state {α : Type _} [MeasurableSpace α] :
    Measurable (fun c : Cfg α => c.state) :=
  measurable_snd.comp (Measurable.of_comap_le le_rfl)

theorem Cfg.measurable_iff {X α : Type _} [MeasurableSpace X] [MeasurableSpace α]
    {f : X → Cfg α} :
    Measurable f
      ↔ Measurable (fun x => (f x).expr) ∧ Measurable (fun x => (f x).state) :=
  ⟨fun hf => ⟨Cfg.measurable_expr.comp hf, Cfg.measurable_state.comp hf⟩,
   fun ⟨h₁, h₂⟩ =>
     (measurable_comap_iff (g := fun c : Cfg α => (c.expr, c.state))).mpr (h₁.prodMk h₂)⟩

@[fun_prop]
theorem Cfg.measurable_mk {α : Type _} [MeasurableSpace α] :
    Measurable (fun (p : Exp α × State α) => Cfg.mk p.1 p.2) :=
  Cfg.measurable_iff.mpr ⟨measurable_fst, measurable_snd⟩

end ProbLang
