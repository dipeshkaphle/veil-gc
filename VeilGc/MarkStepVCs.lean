import Veil
import VeilGc

open VerifiedGc

set_option maxHeartbeats 0

theorem MarkStep_roots_gray_or_black_in_mark (ρ : Type) (σ : Type) (Mutator : Type)
    [Mutator_dec_eq : DecidableEq.{1} Mutator] [Mutator_inhabited : Inhabited.{1} Mutator] (Collector : Type)
    [Collector_dec_eq : DecidableEq.{1} Collector] [Collector_inhabited : Inhabited.{1} Collector] (Ptr : Type)
    [Ptr_dec_eq : DecidableEq.{1} Ptr] [Ptr_inhabited : Inhabited.{1} Ptr] (HeapSize : Nat)
    [heapSizeNonzero : NeZero HeapSize] (Color : Type) [Color_dec_eq : DecidableEq.{1} Color]
    [Color_inhabited : Inhabited.{1} Color] [Color_Enum : @Color_EnumClass Color] (Phase : Type)
    [Phase_dec_eq : DecidableEq.{1} Phase] [Phase_inhabited : Inhabited.{1} Phase] [Phase_Enum : @Phase_EnumClass Phase]
    (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@MarkStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@roots_gray_or_black_in_mark ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  sorry

theorem MarkStep_block_has_color (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
    [Mutator_inhabited : Inhabited.{1} Mutator] (Collector : Type) [Collector_dec_eq : DecidableEq.{1} Collector]
    [Collector_inhabited : Inhabited.{1} Collector] (Ptr : Type) [Ptr_dec_eq : DecidableEq.{1} Ptr]
    [Ptr_inhabited : Inhabited.{1} Ptr] (HeapSize : Nat) [heapSizeNonzero : NeZero HeapSize] (Color : Type)
    [Color_dec_eq : DecidableEq.{1} Color] [Color_inhabited : Inhabited.{1} Color] [Color_Enum : @Color_EnumClass Color]
    (Phase : Type) [Phase_dec_eq : DecidableEq.{1} Phase] [Phase_inhabited : Inhabited.{1} Phase]
    [Phase_Enum : @Phase_EnumClass Phase] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@MarkStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@block_has_color ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited
          Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  classical
  intro hphase t ht hgray ptr hptr
  by_cases htp : t = ptr
  · subst htp
    simp
    exact fun h => Color_Enum.distinct.2.2.2.1 h.symm
  · by_cases hcond :
      (∃ offset, st.field t offset ptr = true) ∧ st.is_block ptr = true ∧
        ¬st.color ptr = Color_EnumClass.blue ∧ ¬st.color ptr = Color_EnumClass.black
    · simp [htp, hcond]
      exact fun h => Color_Enum.distinct.2.2.1 h.symm
    · simp [htp, hcond]
      exact hinv.2.2.2.2.2.2.2.1 ptr hptr

theorem MarkStep_roots_are_allocated (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
    [Mutator_inhabited : Inhabited.{1} Mutator] (Collector : Type) [Collector_dec_eq : DecidableEq.{1} Collector]
    [Collector_inhabited : Inhabited.{1} Collector] (Ptr : Type) [Ptr_dec_eq : DecidableEq.{1} Ptr]
    [Ptr_inhabited : Inhabited.{1} Ptr] (HeapSize : Nat) [heapSizeNonzero : NeZero HeapSize] (Color : Type)
    [Color_dec_eq : DecidableEq.{1} Color] [Color_inhabited : Inhabited.{1} Color] [Color_Enum : @Color_EnumClass Color]
    (Phase : Type) [Phase_dec_eq : DecidableEq.{1} Phase] [Phase_inhabited : Inhabited.{1} Phase]
    [Phase_Enum : @Phase_EnumClass Phase] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@MarkStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@roots_are_allocated ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  classical
  intro hphase t ht hgray ptr hroot
  have hroot_old := hinv.2.2.2.2.2.2.2.2.1 ptr hroot
  constructor
  · exact hroot_old.1
  · by_cases htp : t = ptr
    · subst htp
      simp
      exact fun h => Color_Enum.distinct.2.2.2.2.2.2.1 h.symm
    · by_cases hcond :
        (∃ offset, st.field t offset ptr = true) ∧ st.is_block ptr = true ∧
          ¬st.color ptr = Color_EnumClass.blue ∧ ¬st.color ptr = Color_EnumClass.black
      · simp [htp, hcond]
        exact fun h => Color_Enum.distinct.2.2.2.2.2.1 h.symm
      · simp [htp, hcond]
        exact hroot_old.2

theorem MarkStep_fields_from_allocated (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
    [Mutator_inhabited : Inhabited.{1} Mutator] (Collector : Type) [Collector_dec_eq : DecidableEq.{1} Collector]
    [Collector_inhabited : Inhabited.{1} Collector] (Ptr : Type) [Ptr_dec_eq : DecidableEq.{1} Ptr]
    [Ptr_inhabited : Inhabited.{1} Ptr] (HeapSize : Nat) [heapSizeNonzero : NeZero HeapSize] (Color : Type)
    [Color_dec_eq : DecidableEq.{1} Color] [Color_inhabited : Inhabited.{1} Color] [Color_Enum : @Color_EnumClass Color]
    (Phase : Type) [Phase_dec_eq : DecidableEq.{1} Phase] [Phase_inhabited : Inhabited.{1} Phase]
    [Phase_Enum : @Phase_EnumClass Phase] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@MarkStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@fields_from_allocated ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  classical
  intro hphase t ht hgray parent child hfield
  have hfield_old := hinv.2.2.2.2.2.2.2.2.2.1 off parent child hfield
  constructor
  · exact hfield_old.1
  · by_cases htp : t = parent
    · subst htp
      simp
      exact fun h => Color_Enum.distinct.2.2.2.2.2.2.1 h.symm
    · by_cases hcond :
        (∃ offset, st.field t offset parent = true) ∧ st.is_block parent = true ∧
          ¬st.color parent = Color_EnumClass.blue ∧ ¬st.color parent = Color_EnumClass.black
      · simp [htp, hcond]
        exact fun h => Color_Enum.distinct.2.2.2.2.2.1 h.symm
      · simp [htp, hcond]
        exact hfield_old.2

theorem MarkStep_fields_to_allocated (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
    [Mutator_inhabited : Inhabited.{1} Mutator] (Collector : Type) [Collector_dec_eq : DecidableEq.{1} Collector]
    [Collector_inhabited : Inhabited.{1} Collector] (Ptr : Type) [Ptr_dec_eq : DecidableEq.{1} Ptr]
    [Ptr_inhabited : Inhabited.{1} Ptr] (HeapSize : Nat) [heapSizeNonzero : NeZero HeapSize] (Color : Type)
    [Color_dec_eq : DecidableEq.{1} Color] [Color_inhabited : Inhabited.{1} Color] [Color_Enum : @Color_EnumClass Color]
    (Phase : Type) [Phase_dec_eq : DecidableEq.{1} Phase] [Phase_inhabited : Inhabited.{1} Phase]
    [Phase_Enum : @Phase_EnumClass Phase] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@MarkStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@fields_to_allocated ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  classical
  intro hphase t ht hgray parent child hnotSweep hfield
  have hfield_old := hinv.2.2.2.2.2.2.2.2.2.2.1 off parent child hnotSweep hfield
  constructor
  · exact hfield_old.1
  · by_cases htc : t = child
    · subst htc
      simp
      exact fun h => Color_Enum.distinct.2.2.2.2.2.2.1 h.symm
    · by_cases hcond :
        (∃ offset, st.field t offset child = true) ∧ st.is_block child = true ∧
          ¬st.color child = Color_EnumClass.blue ∧ ¬st.color child = Color_EnumClass.black
      · simp [htc, hcond]
        exact fun h => Color_Enum.distinct.2.2.2.2.2.1 h.symm
      · simp [htc, hcond]
        exact hfield_old.2

theorem MarkStep_free_blocks_have_no_fields (ρ : Type) (σ : Type) (Mutator : Type)
    [Mutator_dec_eq : DecidableEq.{1} Mutator] [Mutator_inhabited : Inhabited.{1} Mutator] (Collector : Type)
    [Collector_dec_eq : DecidableEq.{1} Collector] [Collector_inhabited : Inhabited.{1} Collector] (Ptr : Type)
    [Ptr_dec_eq : DecidableEq.{1} Ptr] [Ptr_inhabited : Inhabited.{1} Ptr] (HeapSize : Nat)
    [heapSizeNonzero : NeZero HeapSize] (Color : Type) [Color_dec_eq : DecidableEq.{1} Color]
    [Color_inhabited : Inhabited.{1} Color] [Color_Enum : @Color_EnumClass Color] (Phase : Type)
    [Phase_dec_eq : DecidableEq.{1} Phase] [Phase_inhabited : Inhabited.{1} Phase] [Phase_Enum : @Phase_EnumClass Phase]
    (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@MarkStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@free_blocks_have_no_fields ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  classical
  intro hphase t ht hgray parent child hparent_block hparent_blue
  by_cases htp : t = parent
  · subst htp
    have h : Color_EnumClass.black = Color_EnumClass.blue := by
      simpa using hparent_blue
    exact False.elim (Color_Enum.distinct.2.2.2.2.2.2.1 h.symm)
  · by_cases hcond :
      (∃ offset, st.field t offset parent = true) ∧ st.is_block parent = true ∧
        ¬st.color parent = Color_EnumClass.blue ∧ ¬st.color parent = Color_EnumClass.black
    · have h : Color_EnumClass.gray = Color_EnumClass.blue := by
        simpa [htp, hcond] using hparent_blue
      exact False.elim (Color_Enum.distinct.2.2.2.2.2.1 h.symm)
    · have hparent_blue_old : st.color parent = Color_EnumClass.blue := by
        simpa [htp, hcond] using hparent_blue
      exact hinv.2.2.2.2.2.2.2.2.2.2.2.1 off parent child hparent_block hparent_blue_old

theorem MarkStep_free_next_unique_predecessor (ρ : Type) (σ : Type) (Mutator : Type)
    [Mutator_dec_eq : DecidableEq.{1} Mutator] [Mutator_inhabited : Inhabited.{1} Mutator] (Collector : Type)
    [Collector_dec_eq : DecidableEq.{1} Collector] [Collector_inhabited : Inhabited.{1} Collector] (Ptr : Type)
    [Ptr_dec_eq : DecidableEq.{1} Ptr] [Ptr_inhabited : Inhabited.{1} Ptr] (HeapSize : Nat)
    [heapSizeNonzero : NeZero HeapSize] (Color : Type) [Color_dec_eq : DecidableEq.{1} Color]
    [Color_inhabited : Inhabited.{1} Color] [Color_Enum : @Color_EnumClass Color] (Phase : Type)
    [Phase_dec_eq : DecidableEq.{1} Phase] [Phase_inhabited : Inhabited.{1} Phase] [Phase_Enum : @Phase_EnumClass Phase]
    (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@MarkStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@free_next_unique_predecessor ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_unique, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro _ t _ _ pred1 pred2 target hp1 hblue1 hp2 hblue2 hn1 hn2 htarget
  have oldblue1 : st.color pred1 = Color_EnumClass.blue := by
    by_cases ht : t = pred1
    · have h : Color_EnumClass.black = Color_EnumClass.blue := by
        simpa [ht] using hblue1
      exact False.elim (Color_Enum.distinct.2.2.2.2.2.2.1 h.symm)
    · simp [ht] at hblue1
      by_cases hcond :
          (∃ offset, st.field t offset pred1 = true) ∧ st.is_block pred1 = true ∧
            ¬st.color pred1 = Color_EnumClass.blue ∧ ¬st.color pred1 = Color_EnumClass.black
      · have h : Color_EnumClass.gray = Color_EnumClass.blue := by
          simpa [hcond] using hblue1
        exact False.elim (Color_Enum.distinct.2.2.2.2.2.1 h.symm)
      · simpa [hcond] using hblue1
  have oldblue2 : st.color pred2 = Color_EnumClass.blue := by
    by_cases ht : t = pred2
    · have h : Color_EnumClass.black = Color_EnumClass.blue := by
        simpa [ht] using hblue2
      exact False.elim (Color_Enum.distinct.2.2.2.2.2.2.1 h.symm)
    · simp [ht] at hblue2
      by_cases hcond :
          (∃ offset, st.field t offset pred2 = true) ∧ st.is_block pred2 = true ∧
            ¬st.color pred2 = Color_EnumClass.blue ∧ ¬st.color pred2 = Color_EnumClass.black
      · have h : Color_EnumClass.gray = Color_EnumClass.blue := by
          simpa [hcond] using hblue2
        exact False.elim (Color_Enum.distinct.2.2.2.2.2.1 h.symm)
      · simpa [hcond] using hblue2
  exact h_unique pred1 pred2 target hp1 oldblue1 hp2 oldblue2 hn1 hn2 htarget

theorem MarkStep_free_blocks_have_list_entry (ρ : Type) (σ : Type) (Mutator : Type)
    [Mutator_dec_eq : DecidableEq.{1} Mutator] [Mutator_inhabited : Inhabited.{1} Mutator] (Collector : Type)
    [Collector_dec_eq : DecidableEq.{1} Collector] [Collector_inhabited : Inhabited.{1} Collector] (Ptr : Type)
    [Ptr_dec_eq : DecidableEq.{1} Ptr] [Ptr_inhabited : Inhabited.{1} Ptr] (HeapSize : Nat)
    [heapSizeNonzero : NeZero HeapSize] (Color : Type) [Color_dec_eq : DecidableEq.{1} Color]
    [Color_inhabited : Inhabited.{1} Color] [Color_Enum : @Color_EnumClass Color] (Phase : Type)
    [Phase_dec_eq : DecidableEq.{1} Phase] [Phase_inhabited : Inhabited.{1} Phase] [Phase_Enum : @Phase_EnumClass Phase]
    (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@MarkStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@free_blocks_have_list_entry ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_free_list, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro hphase t _ hgray hnot_sweep ptr hptr hblue
  have oldblue : st.color ptr = Color_EnumClass.blue := by
    by_cases ht : t = ptr
    · have h : Color_EnumClass.black = Color_EnumClass.blue := by
        simpa [ht] using hblue
      exact False.elim (Color_Enum.distinct.2.2.2.2.2.2.1 h.symm)
    · simp [ht] at hblue
      by_cases hcond :
          (∃ offset, st.field t offset ptr = true) ∧ st.is_block ptr = true ∧
            ¬st.color ptr = Color_EnumClass.blue ∧ ¬st.color ptr = Color_EnumClass.black
      · have h : Color_EnumClass.gray = Color_EnumClass.blue := by
          simpa [hcond] using hblue
        exact False.elim (Color_Enum.distinct.2.2.2.2.2.1 h.symm)
      · simpa [hcond] using hblue
  rcases h_free_list hnot_sweep ptr hptr oldblue with hhead | ⟨pred, hpred_block, hpred_blue, hpred_next⟩
  · exact Or.inl hhead
  · exact Or.inr (by
      refine ⟨pred, hpred_block, ?_, hpred_next⟩
      by_cases ht : t = pred
      · subst pred
        exfalso
        have h : Color_EnumClass.gray = Color_EnumClass.blue := by
          simpa [hpred_blue] using hgray.symm
        exact Color_Enum.distinct.2.2.2.2.2.1 h.symm
      · simp [ht]
        by_cases hcond :
            (∃ offset, st.field t offset pred = true) ∧ st.is_block pred = true ∧
              ¬st.color pred = Color_EnumClass.blue ∧ ¬st.color pred = Color_EnumClass.black
        · exact False.elim (hcond.2.2.1 hpred_blue)
        · simpa [ht, hcond] using hpred_blue)

theorem MarkStep_only_black_to_gray_or_black_during_mark (ρ : Type) (σ : Type) (Mutator : Type)
    [Mutator_dec_eq : DecidableEq.{1} Mutator] [Mutator_inhabited : Inhabited.{1} Mutator] (Collector : Type)
    [Collector_dec_eq : DecidableEq.{1} Collector] [Collector_inhabited : Inhabited.{1} Collector] (Ptr : Type)
    [Ptr_dec_eq : DecidableEq.{1} Ptr] [Ptr_inhabited : Inhabited.{1} Ptr] (HeapSize : Nat)
    [heapSizeNonzero : NeZero HeapSize] (Color : Type) [Color_dec_eq : DecidableEq.{1} Color]
    [Color_inhabited : Inhabited.{1} Color] [Color_Enum : @Color_EnumClass Color] (Phase : Type)
    [Phase_dec_eq : DecidableEq.{1} Phase] [Phase_inhabited : Inhabited.{1} Phase] [Phase_Enum : @Phase_EnumClass Phase]
    (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@MarkStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@only_black_to_gray_or_black_during_mark ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector
          Collector_dec_eq Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq
          Color_inhabited Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  classical
  intro hphase t ht hgray p c hphase' hblack_p hfield
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  by_cases htc : t = c
  · left
    intro hne
    exact (hne htc).elim
  · by_cases htp : t = p
    · subst htp
      have hnotSweep : ¬st.phase = Phase_EnumClass.sweep := by
        intro hsweep
        have hsweep' : Phase_EnumClass.mark = Phase_EnumClass.sweep := by
          simpa [hphase] using hsweep
        simp [Phase_Enum.distinct] at hsweep'
      have hfield_to := h_fields_to off t c hnotSweep (by simpa using hfield)
      have hexists : ∃ offset, st.field t offset c = true := ⟨off, by simpa using hfield⟩
      by_cases hcond_c :
          (∃ offset, st.field t offset c = true) ∧ st.is_block c = true ∧
            ¬st.color c = Color_EnumClass.blue ∧ ¬st.color c = Color_EnumClass.black
      · right
        simp [htc, hcond_c]
      · have hblackc : st.color c = Color_EnumClass.black := by
          by_contra hnotblack
          apply hcond_c
          exact ⟨hexists, hfield_to.1, hfield_to.2, hnotblack⟩
        left
        simp [htc, hblackc]
    · have hblack_p' := hblack_p htp
      by_cases hcond_p :
          (∃ offset, st.field t offset p = true) ∧ st.is_block p = true ∧
            ¬st.color p = Color_EnumClass.blue ∧ ¬st.color p = Color_EnumClass.black
      · have hgrayblack : Color_EnumClass.gray = Color_EnumClass.black := by
          simpa [hcond_p] using hblack_p'
        exact False.elim (Color_Enum.distinct.2.2.2.2.2.2.2.2.2 hgrayblack)
      · have hcolor_p : st.color p = Color_EnumClass.black := by
          simpa [hcond_p] using hblack_p'
        have hcolor_c := h_black_edges off p c hphase' hcolor_p hfield
        simp [htc]
        by_cases hcond_c :
            (∃ offset, st.field t offset c = true) ∧ st.is_block c = true ∧
              ¬st.color c = Color_EnumClass.blue ∧ ¬st.color c = Color_EnumClass.black
        · right
          simp [hcond_c]
        · cases hcolor_c with
          | inl hblackc =>
              left
              simp [hblackc]
          | inr hgrayc =>
              right
              simp [hgrayc]

theorem MarkStep_blue_never_child_outside_sweep (ρ : Type) (σ : Type) (Mutator : Type)
    [Mutator_dec_eq : DecidableEq.{1} Mutator] [Mutator_inhabited : Inhabited.{1} Mutator] (Collector : Type)
    [Collector_dec_eq : DecidableEq.{1} Collector] [Collector_inhabited : Inhabited.{1} Collector] (Ptr : Type)
    [Ptr_dec_eq : DecidableEq.{1} Ptr] [Ptr_inhabited : Inhabited.{1} Ptr] (HeapSize : Nat)
    [heapSizeNonzero : NeZero HeapSize] (Color : Type) [Color_dec_eq : DecidableEq.{1} Color]
    [Color_inhabited : Inhabited.{1} Color] [Color_Enum : @Color_EnumClass Color] (Phase : Type)
    [Phase_dec_eq : DecidableEq.{1} Phase] [Phase_inhabited : Inhabited.{1} Phase] [Phase_Enum : @Phase_EnumClass Phase]
    (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@MarkStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@blue_never_child_outside_sweep ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  classical
  intro x hphase t ht hgray p hnotSweep hp_block hp_blue x_1 hx_1_block
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  by_cases htp : t = p
  · subst htp
    have h : Color_EnumClass.black = Color_EnumClass.blue := by
      simpa using hp_blue
    exact False.elim (Color_Enum.distinct.2.2.2.2.2.2.1 h.symm)
  · by_cases hcond :
      (∃ offset, st.field t offset p = true) ∧ st.is_block p = true ∧
        ¬st.color p = Color_EnumClass.blue ∧ ¬st.color p = Color_EnumClass.black
    · have h : Color_EnumClass.gray = Color_EnumClass.blue := by
        simpa [htp, hcond] using hp_blue
      exact False.elim (Color_Enum.distinct.2.2.2.2.2.1 h.symm)
    · have hp_blue_old : st.color p = Color_EnumClass.blue := by
        simpa [htp, hcond] using hp_blue
      exact h_blue_no_child x p hnotSweep hp_block hp_blue_old x_1 hx_1_block

theorem MarkStep_blue_never_parent (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
    [Mutator_inhabited : Inhabited.{1} Mutator] (Collector : Type) [Collector_dec_eq : DecidableEq.{1} Collector]
    [Collector_inhabited : Inhabited.{1} Collector] (Ptr : Type) [Ptr_dec_eq : DecidableEq.{1} Ptr]
    [Ptr_inhabited : Inhabited.{1} Ptr] (HeapSize : Nat) [heapSizeNonzero : NeZero HeapSize] (Color : Type)
    [Color_dec_eq : DecidableEq.{1} Color] [Color_inhabited : Inhabited.{1} Color] [Color_Enum : @Color_EnumClass Color]
    (Phase : Type) [Phase_dec_eq : DecidableEq.{1} Phase] [Phase_inhabited : Inhabited.{1} Phase]
    [Phase_Enum : @Phase_EnumClass Phase] (χ : State.Label → Type)
    [χ_rep :
      ∀ __veil_f,
        Veil.FieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f)]
    [χ_rep_lawful :
      ∀ __veil_f,
        Veil.LawfulFieldRepresentation (State.Label.toDomain Mutator Collector Ptr HeapSize Color Phase __veil_f)
          (State.Label.toCodomain Mutator Collector Ptr HeapSize Color Phase __veil_f) (χ __veil_f) (χ_rep __veil_f)]
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@MarkStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@blue_never_parent ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited
          Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  classical
  intro x hphase t ht hgray p hp_block hp_blue x_1 hx_1_block
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  by_cases htp : t = p
  · subst htp
    have h : Color_EnumClass.black = Color_EnumClass.blue := by
      simpa using hp_blue
    exact False.elim (Color_Enum.distinct.2.2.2.2.2.2.1 h.symm)
  · by_cases hcond :
      (∃ offset, st.field t offset p = true) ∧ st.is_block p = true ∧
        ¬st.color p = Color_EnumClass.blue ∧ ¬st.color p = Color_EnumClass.black
    · have h : Color_EnumClass.gray = Color_EnumClass.blue := by
        simpa [htp, hcond] using hp_blue
      exact False.elim (Color_Enum.distinct.2.2.2.2.2.1 h.symm)
    · have hp_blue_old : st.color p = Color_EnumClass.blue := by
        simpa [htp, hcond] using hp_blue
      exact h_blue_no_parent x p hp_block hp_blue_old x_1 hx_1_block
