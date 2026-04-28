import Veil
import VeilGc

open VerifiedGc

set_option maxHeartbeats 0

theorem CompleteSweep_fields_to_allocated (ρ : Type) (σ : Type) (Mutator : Type)
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [CompleteSweep_dec_0 :
      delta%
        @VerifiedGc.CompleteSweep._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_dec_eq
          Color_Enum] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@CompleteSweep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited
          Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub CompleteSweep_dec_0 _c)
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
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges_mark, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white, h_no_black_before_mark,
    h_roots_gray_black_mark, h_only_white_blue_sweep_complete, h_color_implies_block, h_gray_only,
    h_no_black_sweep_complete, h_no_white_reset, h_black_edges⟩
  intro hphase hsweep_end hno_white parent child _ hfield
  have hparent_block : st.is_block parent = true := (h_fields_from off parent child hfield).1
  have hparent_not_blue : ¬ st.color parent = Color_EnumClass.blue := (h_fields_from off parent child hfield).2
  have hparent_not_white : ¬ st.color parent = Color_EnumClass.white := hno_white parent hparent_block
  have hparent_not_uncolored : ¬ st.color parent = Color_EnumClass.uncolored := h_block_color parent hparent_block
  have hparent_not_gray : ¬ st.color parent = Color_EnumClass.gray := by
    intro hgray
    have hph := h_gray_only parent hgray
    rw [hphase] at hph
    grind [Phase_Enum.distinct]
  have hparent_black : st.color parent = Color_EnumClass.black := by
    rcases Color_EnumClass.complete (st.color parent) with hun | hblue | hwhite | hgray | hblack
    · exact False.elim (hparent_not_uncolored hun)
    · exact False.elim (hparent_not_blue hblue)
    · exact False.elim (hparent_not_white hwhite)
    · exact False.elim (hparent_not_gray hgray)
    · exact hblack
  have hchild_black := h_black_edges off parent child (Or.inl hphase) hparent_black hfield
  constructor
  · exact h_color_implies_block child (by
      intro hun
      rw [hun] at hchild_black
      grind [Color_Enum.distinct])
  · intro hblue
    rw [hblue] at hchild_black
    grind [Color_Enum.distinct]

theorem CompleteSweep_free_next_unique_predecessor (ρ : Type) (σ : Type) (Mutator : Type)
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [CompleteSweep_dec_0 :
      delta%
        @VerifiedGc.CompleteSweep._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_dec_eq
          Color_Enum] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@CompleteSweep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited
          Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub CompleteSweep_dec_0 _c)
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
  rcases hinv with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, huniq, _⟩
  intro _ _ _ pred1 pred2 target hpred1 hcolor1 hpred2 hcolor2 hnext1 hnext2 htarget
  exact huniq pred1 pred2 target hpred1 hcolor1 hpred2 hcolor2 hnext1 hnext2 htarget

theorem CompleteSweep_free_blocks_have_list_entry (ρ : Type) (σ : Type) (Mutator : Type)
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [CompleteSweep_dec_0 :
      delta%
        @VerifiedGc.CompleteSweep._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_dec_eq
          Color_Enum] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@CompleteSweep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited
          Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub CompleteSweep_dec_0 _c)
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
  grind

theorem CompleteSweep_blue_never_child_outside_sweep (ρ : Type) (σ : Type) (Mutator : Type)
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [CompleteSweep_dec_0 :
      delta%
        @VerifiedGc.CompleteSweep._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_dec_eq
          Color_Enum] :
    ∀ (_c : Collector),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@CompleteSweep.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited
          Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub CompleteSweep_dec_0 _c)
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
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges_mark, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white, h_no_black_before_mark,
    h_roots_gray_black_mark, h_only_white_blue_sweep_complete, h_color_implies_block, h_gray_only,
    h_no_black_sweep_complete, h_no_white_reset, h_black_edges⟩
  intro x hphase hsweep_end hno_white p _ hp_block hp_blue parent hparent_block
  by_cases hfield : st.field parent x p = true
  · have hparent_not_blue : ¬ st.color parent = Color_EnumClass.blue := (h_fields_from x parent p hfield).2
    have hparent_not_white : ¬ st.color parent = Color_EnumClass.white := hno_white parent hparent_block
    have hparent_not_uncolored : ¬ st.color parent = Color_EnumClass.uncolored := h_block_color parent hparent_block
    have hparent_not_gray : ¬ st.color parent = Color_EnumClass.gray := by
      intro hgray
      have hph := h_gray_only parent hgray
      rw [hphase] at hph
      grind [Phase_Enum.distinct]
    have hparent_black : st.color parent = Color_EnumClass.black := by
      rcases Color_EnumClass.complete (st.color parent) with hun | hblue | hwhite | hgray | hblack
      · exact False.elim (hparent_not_uncolored hun)
      · exact False.elim (hparent_not_blue hblue)
      · exact False.elim (hparent_not_white hwhite)
      · exact False.elim (hparent_not_gray hgray)
      · exact hblack
    have hp_black := h_black_edges x parent p (Or.inl hphase) hparent_black hfield
    rw [hp_blue] at hp_black
    exact False.elim (by grind [Color_Enum.distinct])
  · simp [hfield]
