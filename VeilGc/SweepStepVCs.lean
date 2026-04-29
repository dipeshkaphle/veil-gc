import Veil
import VeilGc

open VerifiedGc

set_option maxHeartbeats 0

theorem SweepStep_black_edges_in_sweep (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
        (@SweepStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@black_edges_in_sweep ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  casesm* _ ∧ _
  have h_black : ∀ (off : Fin (HeapSize + 1)) (p c : Ptr),
    st.phase = Phase_EnumClass.sweep ∨ st.phase = Phase_EnumClass.reset_colors →
    st.color p = Color_EnumClass.black → st.field p off c = true → st.color c = Color_EnumClass.black := by assumption
  intro hphase _ _ _ _
  split
  · exact h_black
  · intro off p c hphase_or hcolor_p hneq hfield
    simp [hneq] at hcolor_p
    have hcolor_c := h_black off p c hphase_or hcolor_p hfield
    by_cases heq : th.addrToPtr st.sweep_addr = c
    · subst heq
      rename_i h_not_black
      exact False.elim (h_not_black hcolor_c)
    · simp [heq, hcolor_c]

theorem SweepStep_gray_only_in_mark (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
        (@SweepStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@gray_only_in_mark ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited
          Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  casesm* _ ∧ _
  have h_gray : ∀ (p : Ptr), st.color p = Color_EnumClass.gray → st.phase = Phase_EnumClass.mark ∨ st.phase = Phase_EnumClass.mark_complete ∨ st.phase = Phase_EnumClass.darken_roots ∨ st.phase = Phase_EnumClass.darken_roots_complete := by assumption
  intro hphase _ _ _ _
  split
  · exact h_gray
  · intro p hcolor
    by_cases heq : th.addrToPtr st.sweep_addr = p
    · subst heq
      simp at hcolor
      grind [Color_Enum.distinct]
    · simp [heq] at hcolor
      exact h_gray p hcolor

theorem SweepStep_free_next_after_block (ρ : Type) (σ : Type) (Mutator : Type)
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
        (@SweepStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@free_next_after_block ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  casesm* _ ∧ _
  have h : ∀ (ptr : Ptr), st.is_block ptr = true → st.color ptr = Color_EnumClass.blue → ¬st.next ptr = th.null_ptr → th.ptrToAddr ptr + st.size ptr ≤ th.ptrToAddr (st.next ptr) ∧ (st.phase = Phase_EnumClass.sweep → th.ptrToAddr (st.next ptr) + st.size (st.next ptr) ≤ st.sweep_addr) := by assumption
  have h_sweep_bounds : st.phase = Phase_EnumClass.sweep → th.ptrToAddr th.heap_start ≤ st.sweep_addr ∧ st.sweep_addr ≤ th.ptrToAddr th.heap_start + HeapSize := by assumption
  have h_tail_bounds : st.phase = Phase_EnumClass.sweep → ¬st.free_tail = th.null_ptr → th.ptrToAddr st.free_tail + st.size st.free_tail ≤ st.sweep_addr := by assumption
  have h_next_null : ∀ (ptr : Ptr), st.is_block ptr = true → ¬st.color ptr = Color_EnumClass.blue → st.next ptr = th.null_ptr := by assumption
  have h_size_pos : ∀ (ptr : Ptr), st.is_block ptr = true → 0 < st.size ptr := by assumption
  intro hphase h_sweep_ge h_sweep_lt h_sweep_block h_sweep_color
  have h_raw : ∀ (raw : Nat), th.ptrToAddr (th.addrToPtr raw) = raw := by assumption
  split
  · intro ptr hptr_block hptr_blue hnext_not_null
    have h_old := h ptr hptr_block hptr_blue hnext_not_null
    have h_left : th.ptrToAddr ptr + st.size ptr ≤ th.ptrToAddr (st.next ptr) := h_old.1
    have h_right : st.phase = Phase_EnumClass.sweep → th.ptrToAddr (st.next ptr) + st.size (st.next ptr) ≤ st.sweep_addr + st.size (th.addrToPtr st.sweep_addr) := fun _ => by
      have h1 := h_old.2 hphase
      have hsz := h_size_pos (th.addrToPtr st.sweep_addr) h_sweep_block
      omega
    exact ⟨h_left, h_right⟩
  · by_cases htail_null : st.free_tail = th.null_ptr
    · simp [if_pos htail_null]
      intro ptr hptr_block h_blue hptr_neq hnext_not_null
      have hptr_neq_rev : th.addrToPtr st.sweep_addr ≠ ptr := hptr_neq
      have h_old := h ptr hptr_block (h_blue hptr_neq_rev) hnext_not_null
      exact ⟨by
        simp [if_neg hptr_neq_rev]
        exact h_old.1
      , fun _ => by
        simp [if_neg hptr_neq_rev]
        have h1 := h_old.2 hphase
        have hsz := h_size_pos (th.addrToPtr st.sweep_addr) h_sweep_block
        omega⟩
    · rw [if_neg htail_null]
      intro ptr hptr_block h_blue hptr_neq hnext_not_null
      have hptr_neq_rev : th.addrToPtr st.sweep_addr ≠ ptr := hptr_neq
      by_cases htail : st.free_tail = ptr
      · have h_bound := h_tail_bounds hphase
        have h_tail_bound := h_bound htail_null
        exact ⟨by
          rw [if_neg hptr_neq_rev, if_pos htail]
          rw [←htail]
          rw [h_raw]
          exact h_tail_bound
        , fun _ => by
          rw [if_neg hptr_neq_rev, if_pos htail]
          rw [h_raw]⟩
      · have h_old := h ptr hptr_block (h_blue hptr_neq_rev) (by
          rw [if_neg htail] at hnext_not_null
          exact hnext_not_null)
        exact ⟨by
          rw [if_neg hptr_neq_rev, if_neg htail]
          exact h_old.1
        , fun _ => by
          rw [if_neg hptr_neq_rev, if_neg htail]
          have h1 := h_old.2 hphase
          have hsz := h_size_pos (th.addrToPtr st.sweep_addr) h_sweep_block
          omega⟩

theorem SweepStep_fields_from_allocated (ρ : Type) (σ : Type) (Mutator : Type)
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
        (@SweepStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
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
  rcases hinv with ⟨_, _, _, _, _, _, _, _, _, h_fields_from, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro _ _ _ _ _
  by_cases hblack : st.color (th.addrToPtr st.sweep_addr) = Color_EnumClass.black
  · simp [hblack]
    exact h_fields_from
  · simp [hblack]
    intro off parent child hne hfield
    exact ⟨(h_fields_from off parent child hfield).1, hne, (h_fields_from off parent child hfield).2⟩

theorem SweepStep_free_blocks_have_no_fields (ρ : Type) (σ : Type) (Mutator : Type)
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
        (@SweepStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
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
  rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, h_free_no_fields, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro _ _ _ _ _
  by_cases hblack : st.color (th.addrToPtr st.sweep_addr) = Color_EnumClass.black
  · simp [hblack]
    exact h_free_no_fields
  · simp [hblack]
    intro off parent child hp hblue hne
    exact h_free_no_fields off parent child hp (hblue hne)

theorem SweepStep_field_unique (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
        (@SweepStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@field_unique ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, h_field_unique, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro _ _ _ _ _
  by_cases hblack : st.color (th.addrToPtr st.sweep_addr) = Color_EnumClass.black
  · simp [hblack]
    exact h_field_unique
  · simp [hblack]
    intro off parent child1 child2 _ hfield1 _ hfield2
    exact h_field_unique off parent child1 child2 hfield1 hfield2

theorem SweepStep_field_is_in_bounds (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
        (@SweepStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@field_is_in_bounds ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited
          Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h_field_bounds, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro _ _ _ _ _
  by_cases hblack : st.color (th.addrToPtr st.sweep_addr) = Color_EnumClass.black
  · simp [hblack]
    exact h_field_bounds
  · simp [hblack]
    intro off parent child _ hfield
    exact h_field_bounds off parent child hfield

theorem SweepStep_free_next_unique_predecessor (ρ : Type) (σ : Type) (Mutator : Type)
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
        (@SweepStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
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
  rcases hinv with ⟨_, _, h_null_not_block, _, _, _, h_valid_size, _, _, _, _, _, _, _, _, _, h_next_after, h_unique, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro hphase _ _ hcurr _
  by_cases hblack : st.color (th.addrToPtr st.sweep_addr) = Color_EnumClass.black
  · simp [hblack]
    exact h_unique
  · simp [hblack]
    by_cases htail_null : st.free_tail = th.null_ptr
    · simp [htail_null]
      intro pred1 pred2 target hp1 hc1 hp2 hc2 hn1 hn2 htarget
      by_cases hpred1 : th.addrToPtr st.sweep_addr = pred1
      · simp [hpred1] at hn1
        exact False.elim (htarget hn1.symm)
      · by_cases hpred2 : th.addrToPtr st.sweep_addr = pred2
        · simp [hpred2] at hn2
          exact False.elim (htarget hn2.symm)
        · exact h_unique pred1 pred2 target hp1 (hc1 hpred1) hp2 (hc2 hpred2)
            (by simpa [hpred1] using hn1) (by simpa [hpred2] using hn2) htarget
    · simp [htail_null]
      intro pred1 pred2 target hp1 hc1 hp2 hc2 hn1 hn2 htarget
      have haddr : th.ptrToAddr (th.addrToPtr st.sweep_addr) = st.sweep_addr := has.2.2.2.1 st.sweep_addr
      have hcurr_size : 0 < st.size (th.addrToPtr st.sweep_addr) := h_valid_size (th.addrToPtr st.sweep_addr) hcurr
      have no_old_points_curr :
          ∀ pred,
            st.is_block pred = true →
            st.color pred = Color_EnumClass.blue →
            st.next pred = th.addrToPtr st.sweep_addr →
            False := by
        intro pred hpred hpred_blue hnext
        have hnext_ne : ¬st.next pred = th.null_ptr := by
          intro hnull
          have hcurr_null : th.addrToPtr st.sweep_addr = th.null_ptr := by
            rw [← hnext, hnull]
          rw [hcurr_null] at hcurr
          simp [h_null_not_block] at hcurr
        have hle := (h_next_after pred hpred hpred_blue hnext_ne).2 hphase
        rw [hnext, haddr] at hle
        omega
      by_cases hpred1_curr : th.addrToPtr st.sweep_addr = pred1
      · simp [hpred1_curr] at hn1
        exact False.elim (htarget hn1.symm)
      · by_cases hpred2_curr : th.addrToPtr st.sweep_addr = pred2
        · simp [hpred2_curr] at hn2
          exact False.elim (htarget hn2.symm)
        · by_cases hpred1_tail : st.free_tail = pred1
          · by_cases hpred2_tail : st.free_tail = pred2
            · exact hpred1_tail.symm.trans hpred2_tail
            · have hn1' : th.addrToPtr st.sweep_addr = target := by
                simpa [hpred1_curr, hpred1_tail] using hn1
              have hn2' : st.next pred2 = target := by
                simpa [hpred2_curr, hpred2_tail] using hn2
              have hnext2 : st.next pred2 = th.addrToPtr st.sweep_addr := by
                rw [hn2', ← hn1']
              exact False.elim (no_old_points_curr pred2 hp2 (hc2 hpred2_curr) hnext2)
          · by_cases hpred2_tail : st.free_tail = pred2
            · have hn1' : st.next pred1 = target := by
                simpa [hpred1_curr, hpred1_tail] using hn1
              have hn2' : th.addrToPtr st.sweep_addr = target := by
                simpa [hpred2_curr, hpred2_tail] using hn2
              have hnext1 : st.next pred1 = th.addrToPtr st.sweep_addr := by
                rw [hn1', ← hn2']
              exact False.elim (no_old_points_curr pred1 hp1 (hc1 hpred1_curr) hnext1)
            · exact h_unique pred1 pred2 target hp1 (hc1 hpred1_curr) hp2 (hc2 hpred2_curr)
                (by simpa [hpred1_curr, hpred1_tail] using hn1)
                (by simpa [hpred2_curr, hpred2_tail] using hn2) htarget

theorem SweepStep_swept_free_blocks_have_list_entry (ρ : Type) (σ : Type) (Mutator : Type)
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
        (@SweepStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@swept_free_blocks_have_list_entry ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  rcases hinv with ⟨_, _, h_null_not_block, _, h_no_overlap, _, h_valid_size, _, _, _, _, _, _, _, _, _, h_next_after, _, _, h_swept, h_tail_free, h_head_tail, h_tail_next_null, h_tail_before, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro hphase _ _ hcurr _
  have haddr : th.ptrToAddr (th.addrToPtr st.sweep_addr) = st.sweep_addr := has.2.2.2.1 st.sweep_addr
  have before_or_curr :
      ∀ ptr,
        st.is_block ptr = true →
        th.ptrToAddr ptr + st.size ptr ≤ st.sweep_addr + st.size (th.addrToPtr st.sweep_addr) →
          ptr = th.addrToPtr st.sweep_addr ∨ th.ptrToAddr ptr + st.size ptr ≤ st.sweep_addr := by
    intro ptr hptr hend
    by_cases hptr_curr : ptr = th.addrToPtr st.sweep_addr
    · exact Or.inl hptr_curr
    · exact Or.inr (by
        by_cases hlt : th.ptrToAddr ptr < st.sweep_addr
        · have hsep := h_no_overlap ptr (th.addrToPtr st.sweep_addr) hptr hcurr (by simpa [haddr] using hlt)
          simpa [haddr] using hsep
        · have hge : st.sweep_addr ≤ th.ptrToAddr ptr := le_of_not_gt hlt
          by_cases heq : th.ptrToAddr ptr = st.sweep_addr
          · have hptr_eq : ptr = th.addrToPtr st.sweep_addr := by
              calc
                ptr = th.addrToPtr (th.ptrToAddr ptr) := (has.2.1 ptr).symm
                _ = th.addrToPtr st.sweep_addr := by rw [heq]
            exact False.elim (hptr_curr hptr_eq)
          · have hgt : st.sweep_addr < th.ptrToAddr ptr := lt_of_le_of_ne hge (Ne.symm heq)
            have hsep := h_no_overlap (th.addrToPtr st.sweep_addr) ptr hcurr hptr (by simpa [haddr] using hgt)
            have hsize := h_valid_size ptr hptr
            omega)
  by_cases hblack : st.color (th.addrToPtr st.sweep_addr) = Color_EnumClass.black
  · simp [hblack]
    intro _ ptr hptr hblue hend
    rcases before_or_curr ptr hptr hend with hptr_curr | hbefore
    · subst ptr
      exfalso
      have h : Color_EnumClass.black = Color_EnumClass.blue := by
        simpa [hblack] using hblue
      exact Color_Enum.distinct.2.2.2.2.2.2.1 h.symm
    · exact h_swept hphase ptr hptr hblue hbefore
  · simp [hblack]
    by_cases htail : st.free_tail = th.null_ptr
    · simp [htail]
      intro _ ptr hptr hblue hend
      rcases before_or_curr ptr hptr hend with hptr_curr | hbefore
      · exact Or.inl hptr_curr
      · exact Or.inr (by
          have hptr_ne_curr : ¬th.addrToPtr st.sweep_addr = ptr := by
            intro h
            subst ptr
            rw [haddr] at hbefore
            have hs := h_valid_size (th.addrToPtr st.sweep_addr) hcurr
            omega
          rcases h_swept hphase ptr hptr (hblue hptr_ne_curr) hbefore with hhead | ⟨pred, hpred_block, hpred_blue, hpred_next⟩
          · subst ptr
            have hhead_null : st.free_head = th.null_ptr := (h_head_tail hphase).mpr htail
            simp [hhead_null, h_null_not_block] at hptr
          · refine ⟨pred, hpred_block, ?_, ?_⟩
            · intro hpred_curr
              exact hpred_blue
            · have hpred_ne_curr : ¬th.addrToPtr st.sweep_addr = pred := by
                intro hpred_curr
                subst pred
                have hnext_ne : ¬st.next (th.addrToPtr st.sweep_addr) = th.null_ptr := by
                  intro hnull
                  rw [hnull] at hpred_next
                  subst ptr
                  simp [h_null_not_block] at hptr
                have hnext_le := (h_next_after (th.addrToPtr st.sweep_addr) hcurr hpred_blue hnext_ne).1
                rw [hpred_next, haddr] at hnext_le
                have hs := h_valid_size ptr hptr
                omega
              simp [hpred_ne_curr, hpred_next])
    · simp [htail]
      intro _ ptr hptr hblue hend
      rcases before_or_curr ptr hptr hend with hptr_curr | hbefore
      · exact Or.inr (by
          have htail_ne_curr : ¬th.addrToPtr st.sweep_addr = st.free_tail := by
            intro htail_curr
            have hbefore_tail := h_tail_before hphase htail
            rw [← htail_curr, haddr] at hbefore_tail
            have hs := h_valid_size (th.addrToPtr st.sweep_addr) hcurr
            omega
          refine ⟨st.free_tail, ?_, ?_, ?_⟩
          · exact (h_tail_free hphase htail).1
          · intro _
            exact (h_tail_free hphase htail).2
          · simp [hptr_curr, htail_ne_curr])
      · have hptr_ne_curr : ¬th.addrToPtr st.sweep_addr = ptr := by
          intro h
          subst ptr
          rw [haddr] at hbefore
          have hs := h_valid_size (th.addrToPtr st.sweep_addr) hcurr
          omega
        rcases h_swept hphase ptr hptr (hblue hptr_ne_curr) hbefore with hhead | ⟨pred, hpred_block, hpred_blue, hpred_next⟩
        · exact Or.inl hhead
        · exact Or.inr (by
            refine ⟨pred, hpred_block, ?_, ?_⟩
            · intro _
              exact hpred_blue
            · have hpred_ne_curr : ¬th.addrToPtr st.sweep_addr = pred := by
                intro hpred_curr
                subst pred
                have hnext_ne : ¬st.next (th.addrToPtr st.sweep_addr) = th.null_ptr := by
                  intro hnull
                  rw [hnull] at hpred_next
                  subst ptr
                  simp [h_null_not_block] at hptr
                have hnext_le := (h_next_after (th.addrToPtr st.sweep_addr) hcurr hpred_blue hnext_ne).1
                rw [hpred_next, haddr] at hnext_le
                have hs := h_valid_size ptr hptr
                omega
              have hpred_ne_tail : ¬st.free_tail = pred := by
                intro hpred_tail
                have htail_next := h_tail_next_null hphase htail
                rw [hpred_tail, hpred_next] at htail_next
                rw [htail_next] at hptr
                simp [h_null_not_block] at hptr
              simp [hpred_ne_curr, hpred_ne_tail, hpred_next])

theorem SweepStep_sweep_addr_points_to_block (ρ : Type) (σ : Type) (Mutator : Type)
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
        (@SweepStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@sweep_addr_points_to_block ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  rcases hinv with ⟨_, _, _, _, _, h_next_by_size, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  intro _ _ _ hcurr _ _ hnext_lt
  have haddr : th.ptrToAddr (th.addrToPtr st.sweep_addr) = st.sweep_addr := has.2.2.2.1 st.sweep_addr
  have hnext := h_next_by_size (th.addrToPtr st.sweep_addr) hcurr
  rw [haddr] at hnext
  rcases hnext with hnext | hnext
  · omega
  · exact hnext

theorem SweepStep_blue_never_parent (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
        (@SweepStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
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
  rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_blue_never_parent, _, _, _, _⟩
  intro _ _ _ _ _
  by_cases hblack : st.color (th.addrToPtr st.sweep_addr) = Color_EnumClass.black
  · simp [hblack]
    exact h_blue_never_parent
  · simp [hblack]
    intro off parent hparent hblue child hchild hne
    exact h_blue_never_parent off parent hparent (hblue hne) child hchild

theorem SweepStep_reachables_still_black_after_unreachables_sweeping (ρ : Type) (σ : Type) (Mutator : Type)
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
        (@SweepStep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _c)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@reachables_still_black_after_unreachables_sweeping ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector
          Collector_dec_eq Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq
          Color_inhabited Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h_reach_black, _, _⟩
  intro _ _ _ _ _
  by_cases hblack : st.color (th.addrToPtr st.sweep_addr) = Color_EnumClass.black
  · simp [hblack]
    exact h_reach_black
  · simp [hblack]
    intro off parent child hphase hparent_black hparent_ne hfield
    have hparent_black_old : st.color parent = Color_EnumClass.black := by
      simpa [hparent_ne] using hparent_black
    have hchild_black := h_reach_black off parent child hphase hparent_black_old hfield
    by_cases hchild : th.addrToPtr st.sweep_addr = child
    · exfalso
      exact hblack (by simpa [hchild] using hchild_black)
    · simpa [hchild] using hchild_black
