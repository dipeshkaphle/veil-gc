import Veil
import VeilGc

open VerifiedGc
open VerifiedGc.Color_EnumClass

theorem Allocate_block_has_color (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
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
  intro hphase hreq t ht hb hentry hle
  split
  · intro ptr hptr
    by_cases htptr : t = ptr
    · simp [htptr]
      exact fun h => Color_Enum.distinct.2.1 h.symm
    · by_cases hr : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = ptr
      · simp [htptr, hr]
        exact fun h => Color_Enum.distinct.1 h.symm
      · simp [htptr, hr]
        exact hinv.2.2.2.2.2.2.2.1 ptr (hptr hr)
  · intro ptr hptr
    by_cases htptr : t = ptr
    · simp [htptr]
      exact fun h => Color_Enum.distinct.2.1 h.symm
    · simp [htptr]
      exact hinv.2.2.2.2.2.2.2.1 ptr hptr

theorem Allocate_block_has_valid_size (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@block_has_valid_size ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hphase hreq t ht hb hentry hle
  split
  · intro ptr hptr
    by_cases htptr : t = ptr
    · simp [htptr]
      exact hreq
    · by_cases hr : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = ptr
      · simp [htptr, hr]
        omega
      · simp [htptr, hr]
        exact hinv.2.2.2.2.2.2.1 ptr (hptr hr)
  · intro ptr hptr
    by_cases htptr : t = ptr
    · simp [htptr]
      exact hreq
    · simp [htptr]
      exact hinv.2.2.2.2.2.2.1 ptr hptr

theorem Allocate_block_next_by_size_is_block (ρ : Type) (σ : Type) (Mutator : Type)
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
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@block_next_by_size_is_block ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hphase hreq t ht hb hentry hle
  split
  · intro p hp
    by_cases htp : t = p
    · subst p
      right
      intro hbad
      simp at hbad
    · by_cases hrp : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = p
      · subst p
        have hold := hinv.2.2.2.2.2.1 t ht
        have htp' : ¬ t = th.addrToPtr (th.ptrToAddr t + ↑reqSize) := by
          exact htp
        rcases hold with hold | hold
        · left
          simp [htp', has.2.2.2.1]
          omega
        · right
          intro hnew
          simp [htp', has.2.2.2.1]
          have haddr : th.ptrToAddr t + ↑reqSize + (st.size t - ↑reqSize) =
              th.ptrToAddr t + st.size t := by
            omega
          have hptr : th.addrToPtr (th.ptrToAddr t + ↑reqSize + (st.size t - ↑reqSize)) =
              th.addrToPtr (th.ptrToAddr t + st.size t) := by
            rw [haddr]
          rwa [hptr]
      · have hold := hinv.2.2.2.2.2.1 p (hp hrp)
        rcases hold with hold | hold
        · left
          simpa [htp, hrp] using hold
        · right
          intro _
          simpa [htp, hrp] using hold
  · intro p hp
    by_cases htp : t = p
    · subst p
      have hold := hinv.2.2.2.2.2.1 t ht
      rcases hold with hold | hold
      · left
        simp
        omega
      · right
        simp
        have this : th.ptrToAddr t + ↑reqSize = th.ptrToAddr t + st.size t := by
          omega
        simpa [this] using hold
    · have hold := hinv.2.2.2.2.2.1 p hp
      simpa [htp] using hold

theorem Allocate_blocks_do_not_overlap (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@blocks_do_not_overlap ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hphase hreq t ht hb hentry hle
  have addr_inj : ∀ {a b : Ptr}, th.ptrToAddr a = th.ptrToAddr b → a = b := by
    intro a b haddr
    have hc := congrArg th.addrToPtr haddr
    simpa [has.2.1 a, has.2.1 b] using hc
  split
  · intro p q hp hq hpq
    by_cases hpt : p = t
    · subst p
      by_cases hqr : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = q
      · subst q
        simp [has.2.2.2.1]
      · simp
        have hqOld : st.is_block q = true := hq hqr
        have hOld := hinv.2.2.2.2.1 t q ht hqOld hpq
        omega
    · by_cases hpr : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = p
      · subst p
        have hpt' : ¬ t = th.addrToPtr (th.ptrToAddr t + ↑reqSize) := by
          intro htEq
          exact hpt htEq.symm
        by_cases hqr : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = q
        · subst q
          rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hpq
          omega
        · simp [hpt', has.2.2.2.1]
          have hqOld : st.is_block q = true := hq hqr
          have htq : th.ptrToAddr t < th.ptrToAddr q := by
            rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hpq
            omega
          have hOld := hinv.2.2.2.2.1 t q ht hqOld htq
          omega
      · have hpOld : st.is_block p = true := hp hpr
        have htp2 : ¬ t = p := by
          intro h
          exact hpt h.symm
        by_cases hqr : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = q
        · subst q
          simp [htp2, hpr, has.2.2.2.1]
          rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hpq
          by_cases hlt : th.ptrToAddr p < th.ptrToAddr t
          · have hOld := hinv.2.2.2.2.1 p t hpOld ht hlt
            omega
          · have hneAddr : th.ptrToAddr p ≠ th.ptrToAddr t := by
              intro heq
              exact hpt (addr_inj heq)
            have htp : th.ptrToAddr t < th.ptrToAddr p := by
              omega
            have hOld := hinv.2.2.2.2.1 t p ht hpOld htp
            omega
        · simp [htp2, hpr]
          have hqOld : st.is_block q = true := hq hqr
          exact hinv.2.2.2.2.1 p q hpOld hqOld hpq
  · intro p q hp hq hpq
    by_cases hpt : p = t
    · subst p
      simp only [if_true]
      have hOld : th.ptrToAddr t + st.size t ≤ th.ptrToAddr q :=
        hinv.2.2.2.2.1 t q ht hq hpq
      omega
    · have htp2 : ¬ t = p := by
        intro h
        exact hpt h.symm
      simp [htp2]
      exact hinv.2.2.2.2.1 p q hp hq hpq

theorem Allocate_block_fits_in_heap (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@block_fits_in_heap ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited
          Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hphase hreq t ht hb hentry hle
  split
  · intro ptr hptr
    by_cases htptr : t = ptr
    · subst ptr
      simp
      have hfit := hinv.2.2.2.1 t ht
      omega
    · by_cases hr : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = ptr
      · subst ptr
        simp [htptr]
        let raw := th.ptrToAddr t + ↑reqSize
        have htHeap := hinv.2.1 t ht
        have hfit := hinv.2.2.2.1 t ht
        have hrawLower : th.ptrToAddr th.heap_start ≤ raw := by
          dsimp [raw]
          omega
        have hrawUpper : raw < th.ptrToAddr th.heap_start + HeapSize := by
          dsimp [raw]
          omega
        have hround := has.2.2.1 raw hrawLower hrawUpper
        rw [hround]
        omega
      · simp [htptr, hr]
        exact hinv.2.2.2.1 ptr (hptr hr)
  · intro ptr hptr
    by_cases htptr : t = ptr
    · subst ptr
      simp
      have hfit := hinv.2.2.2.1 t ht
      omega
    · simp [htptr]
      exact hinv.2.2.2.1 ptr hptr

theorem Allocate_null_ptr_not_block (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@null_ptr_not_block ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited
          Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hphase hreq t ht hb hentry hle
  split
  · constructor
    · intro hnull
      have htHeap := hinv.2.1 t ht
      have hfit := hinv.2.2.2.1 t ht
      have haddr : th.ptrToAddr t + ↑reqSize = th.ptrToAddr th.null_ptr := by
        have hc := congrArg th.ptrToAddr hnull
        rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hc
        exact hc
      have hnullLower : th.ptrToAddr th.heap_start ≤ th.ptrToAddr th.null_ptr := by
        rw [← haddr]
        omega
      have hnullUpper := has.2.2.2.2 hnullLower
      omega
    · exact hinv.2.2.1
  · exact hinv.2.2.1

theorem Allocate_block_always_lies_in_heap (ρ : Type) (σ : Type) (Mutator : Type)
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
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@block_always_lies_in_heap ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hphase hreq t ht hb hentry hle
  split
  · intro ptr hptr
    by_cases hr : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = ptr
    · subst ptr
      constructor
      · rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
        have htHeap := hinv.2.1 t ht
        omega
      · rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
        have hfit := hinv.2.2.2.1 t ht
        omega
    · exact hinv.2.1 ptr (hptr hr)
  · intro ptr hptr
    exact hinv.2.1 ptr hptr


theorem Allocate_roots_are_allocated (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
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
  intro hphase hreq t ht hblue hlist hsize
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  split
  · intro ptr hptr
    by_cases htptr : t = ptr
    · subst ptr
      constructor
      · intro _
        exact ht
      · intro h
        have h' : white = blue := by
          simpa using h
        exact Color_Enum.distinct.2.2.2.2.1 h'.symm
    · by_cases hr : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = ptr
      · subst ptr
        have hroot_old := h_roots_alloc (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) hptr
        have hblock_old : st.is_block (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) = true := hroot_old.1
        have ht_lt_rem : th.ptrToAddr t < th.ptrToAddr (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) := by
          rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
          omega
        have hoverlap := h_no_overlap t (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) ht hblock_old ht_lt_rem
        rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hoverlap
        have : False := by
          omega
        exact this.elim
      · have hroot_old := h_roots_alloc ptr hptr
        constructor
        · intro _
          exact hroot_old.1
        · simpa [htptr, hr] using hroot_old.2
  · intro ptr hptr
    by_cases htptr : t = ptr
    · subst ptr
      constructor
      · exact ht
      · intro h
        have h' : white = blue := by
          simpa using h
        exact Color_Enum.distinct.2.2.2.2.1 h'.symm
    · have hroot_old := h_roots_alloc ptr hptr
      constructor
      · exact hroot_old.1
      · simpa [htptr] using hroot_old.2

theorem Allocate_fields_from_allocated (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
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
  intro hphase hreq t ht hblue hlist hsize
  split
  · intro off parent child hne_t hne_rem hfield
    have hfield_old := hinv.2.2.2.2.2.2.2.2.2.1 off parent child hfield
    constructor
    · intro _
      exact hfield_old.1
    · simpa [hne_t, hne_rem] using hfield_old.2
  · intro off parent child hne_t hfield
    have hfield_old := hinv.2.2.2.2.2.2.2.2.2.1 off parent child hfield
    constructor
    · exact hfield_old.1
    · simpa [hne_t] using hfield_old.2

theorem Allocate_fields_to_allocated (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
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
  intro hphase hreq t ht hblue hlist hsize
  split
  · intro off parent child hnotSweep hne_parent_t hne_parent_rem hfield
    have hfield_old := hinv.2.2.2.2.2.2.2.2.2.2.1 off parent child hnotSweep hfield
    constructor
    · intro _
      exact hfield_old.1
    · by_cases htc : t = child
      · subst child
        exact False.elim (hfield_old.2 hblue)
      · by_cases hremc : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = child
        · subst child
          have hrem_block := hfield_old.1
          have ht_lt_rem : th.ptrToAddr t < th.ptrToAddr (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) := by
            rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
            omega
          have hoverlap := hinv.2.2.2.2.1 t (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) ht hrem_block ht_lt_rem
          rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hoverlap
          omega
        · simpa [htc, hremc] using hfield_old.2
  · intro off parent child hnotSweep hne_parent_t hfield
    have hfield_old := hinv.2.2.2.2.2.2.2.2.2.2.1 off parent child hnotSweep hfield
    constructor
    · exact hfield_old.1
    · by_cases htc : t = child
      · subst child
        exact False.elim (hfield_old.2 hblue)
      · simpa [htc] using hfield_old.2

theorem Allocate_free_blocks_have_no_fields (ρ : Type) (σ : Type) (Mutator : Type)
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
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
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
  intro hphase hreq t ht hblue hlist hsize
  split
  · intro off parent child hparent_block hparent_blue hne_t hne_rem
    have hparent_blue_old : st.color parent = blue  := by
      simpa [hne_t, hne_rem] using hparent_blue
    exact hinv.2.2.2.2.2.2.2.2.2.2.2.1 off parent child (hparent_block hne_rem) hparent_blue_old
  · intro off parent child hparent_block hparent_blue hne_t
    have hparent_blue_old : st.color parent = blue := by
      simpa [hne_t] using hparent_blue
    exact hinv.2.2.2.2.2.2.2.2.2.2.2.1 off parent child hparent_block hparent_blue_old

theorem Allocate_field_unique (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
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
  intro hphase hreq t ht hblue hlist hsize
  split
  · intro off parent child1 child2 hne_t₁ hne_rem₁ hfield1 hne_t₂ hne_rem₂ hfield2
    exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.1 off parent child1 child2 hfield1 hfield2
  · intro off parent child1 child2 hne_t₁ hfield1 hne_t₂ hfield2
    exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.1 off parent child1 child2 hfield1 hfield2

theorem Allocate_field_is_in_bounds (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
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
  intro hphase hreq t ht hblue hlist hsize
  split
  · intro off parent child hne_t hne_rem hfield
    have hbounds_old := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1 off parent child hfield
    simpa [hne_t, hne_rem] using hbounds_old
  · intro off parent child hne_t hfield
    have hbounds_old := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1 off parent child hfield
    simpa [hne_t] using hbounds_old

theorem Allocate_free_block_next_wellformed (ρ : Type) (σ : Type) (Mutator : Type)
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
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@free_block_next_wellformed ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  classical
  intro hphase hreq t ht hblue hlist hsize
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  split
  · intro ptr hptr_block hptr_blue hne_t hptr_next_ne
    have ht_ne_rem : ¬t = th.addrToPtr (th.ptrToAddr t + ↑reqSize) := by
      intro h
      have hc := congrArg th.ptrToAddr h
      rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hc
      have hpos := hreq
      omega
    by_cases hremp : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = ptr
    · subst ptr
      have hnext_ne : ¬st.next t = th.null_ptr := by
        simpa [hne_t] using hptr_next_ne
      have hnext_old := h_free_next_wf t ht hblue hnext_ne
      constructor
      · intro _
        simpa [hne_t] using hnext_old.1
      · by_cases hself : st.next t = t
        · have hafter := h_free_next_after t ht hblue hnext_ne
          have : False := by
            have hafter' : th.ptrToAddr t + st.size t ≤ th.ptrToAddr t := by
              simpa [hself] using hafter
            omega
          exact this.elim
        · by_cases hremnext : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = st.next t
          · have ht_next : ¬t = st.next t := by
              intro h
              exact hne_t (h.trans hremnext.symm)
            simp [ht_ne_rem, ht_next, hremnext]
          · have hcolor := hnext_old.2
            have ht_next : ¬t = st.next t := by
              intro h
              exact hself h.symm
            simp [ht_ne_rem, ht_next, hremnext, hcolor]
    · by_cases hpred : st.is_block ptr = true ∧ st.color ptr = blue ∧ st.next ptr = t
      · constructor
        · intro hne
          simp [hne_t, hremp, hpred] at hne
        · simp [ht_ne_rem, hne_t, hremp, hpred]
      · have hptr_block_old : st.is_block ptr = true := hptr_block hremp
        have hptr_blue_old : st.color ptr = blue := by
          simpa [hne_t, hremp] using hptr_blue
        have hnext_ne : ¬st.next ptr = th.null_ptr := by
          simpa [hne_t, hremp, hpred] using hptr_next_ne
        have hnext_old := h_free_next_wf ptr hptr_block_old hptr_blue_old hnext_ne
        constructor
        · intro _
          simpa [hne_t, hremp, hpred] using hnext_old.1
        · have hnext_not_t : st.next ptr ≠ t := by
            intro hnext_eq
            exact hpred ⟨hptr_block_old, hptr_blue_old, hnext_eq⟩
          by_cases hremnext : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = st.next ptr
          · have ht_next : ¬t = st.next ptr := by
              intro h
              exact hnext_not_t h.symm
            simp [ht_ne_rem, hne_t, hremp, hpred, ht_next, hremnext]
          · have hcolor := hnext_old.2
            have ht_next : ¬t = st.next ptr := by
              intro h
              exact hnext_not_t h.symm
            simp [ht_ne_rem, hne_t, hremp, hpred, ht_next, hremnext, hcolor]
  · intro ptr hptr_block hptr_blue hne_t hptr_next_ne
    by_cases hpred : st.is_block ptr = true ∧ st.color ptr = blue ∧ st.next ptr = t
    · have hnext_ne : ¬st.next t = th.null_ptr := by
        simpa [hne_t, hpred] using hptr_next_ne
      have hnext_old := h_free_next_wf t ht hblue hnext_ne
      constructor
      · simpa [hne_t, hpred] using hnext_old.1
      · by_cases hself : st.next t = t
        · have hafter := h_free_next_after t ht hblue hnext_ne
          have : False := by
            have hafter' : th.ptrToAddr t + st.size t ≤ th.ptrToAddr t := by
              simpa [hself] using hafter
            omega
          exact this.elim
        · have hcolor := hnext_old.2
          have ht_next : ¬t = st.next t := by
            intro h
            exact hself h.symm
          simpa [hne_t, hpred, ht_next] using hcolor
    · have hptr_blue_old : st.color ptr = blue := by
        simpa [hne_t] using hptr_blue
      have hnext_ne : ¬st.next ptr = th.null_ptr := by
        simpa [hne_t, hpred] using hptr_next_ne
      have hnext_old := h_free_next_wf ptr hptr_block hptr_blue_old hnext_ne
      constructor
      · simpa [hne_t, hpred] using hnext_old.1
      · have hnext_not_t : st.next ptr ≠ t := by
          intro hnext_eq
          exact hpred ⟨hptr_block, hptr_blue_old, hnext_eq⟩
        have ht_next : ¬t = st.next ptr := by
          intro h
          exact hnext_not_t h.symm
        have hcolor := hnext_old.2
        simpa [hne_t, hpred, ht_next] using hcolor

theorem Allocate_free_head_is_free_or_null (ρ : Type) (σ : Type) (Mutator : Type)
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
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@free_head_is_free_or_null ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hphase hreq t ht hblue hlist hsize
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  split
  · by_cases hhead : t = st.free_head
    · subst t
      simp
      right
      intro htrem
      have haddr : th.ptrToAddr st.free_head = th.ptrToAddr (th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize)) := by
        exact congrArg th.ptrToAddr htrem
      rw [has.2.2.2.1 (th.ptrToAddr st.free_head + ↑reqSize)] at haddr
      omega
    · rcases h_free_head_ok with hnull | hfree
      · simpa [hhead] using Or.inl hnull
      · simpa [hhead, hfree.2] using
          (Or.inr ⟨by intro hrem; exact hfree.1, hfree.2⟩ :
            st.free_head = th.null_ptr ∨
              (¬th.addrToPtr (th.ptrToAddr t + ↑reqSize) = st.free_head → st.is_block st.free_head = true) ∧
                st.color st.free_head = blue)
  · by_cases hhead : t = st.free_head
    · subst t
      by_cases hnext_null : st.next st.free_head = th.null_ptr
      · simpa using Or.inl hnext_null
      · simp
        right
        have hnext := h_free_next_wf st.free_head ht hblue hnext_null
        constructor
        · exact hnext.1
        · by_cases hself : st.free_head = st.next st.free_head
          · have hafter := h_free_next_after st.free_head ht hblue hnext_null
            rw [← hself] at hafter
            have hpos := h_valid_size st.free_head ht
            omega
          · simpa [hself] using hnext.2
    · rcases h_free_head_ok with hnull | hfree
      · simpa [hhead] using Or.inl hnull
      · simpa [hhead] using Or.inr hfree

theorem Allocate_free_next_after_block (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
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
  intro hphase hreq t ht hblue hlist hsize
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  split
  · intro ptr hptr_block hptr_blue hne_t hptr_next_ne
    by_cases hremp : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = ptr
    · subst ptr
      have hnext_ne : ¬st.next t = th.null_ptr := by
        simpa [hne_t, hremp] using hptr_next_ne
      have hafter_old := h_free_next_after t ht hblue hnext_ne
      have hsum :
          th.ptrToAddr (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) + (st.size t - ↑reqSize) =
            th.ptrToAddr t + st.size t := by
        rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
        omega
      have hafter_new :
          th.ptrToAddr (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) + (st.size t - ↑reqSize) ≤
            th.ptrToAddr (st.next t) := by
        simpa [hsum] using hafter_old
      simpa [hne_t, hremp] using hafter_new
    · by_cases hpred : st.is_block ptr = true ∧ st.color ptr = blue ∧ st.next ptr = t
      · have hptr_block_old : st.is_block ptr = true := hptr_block hremp
        have hptr_blue_old : st.color ptr = blue := by
          simpa [hne_t, hremp] using hptr_blue
        have ht_ne_null : t ≠ th.null_ptr := by
          intro ht_null
          have : st.is_block th.null_ptr = true := by
            simpa [ht_null] using ht
          simpa [h_null_not_block] using this
        have hnext_ne_old : ¬st.next ptr = th.null_ptr := by
          intro hnext_eq
          exact ht_ne_null (by simpa [hpred.2.2] using hnext_eq)
        have hafter_old := h_free_next_after ptr hptr_block_old hptr_blue_old hnext_ne_old
        have hle : th.ptrToAddr t ≤ th.ptrToAddr (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) := by
          rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
          omega
        have hafter_new :
            th.ptrToAddr ptr + st.size ptr ≤ th.ptrToAddr (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) := by
          omega
        simpa [hne_t, hremp, hpred] using hafter_new
      · have hptr_block_old : st.is_block ptr = true := hptr_block hremp
        have hptr_blue_old : st.color ptr = blue := by
          simpa [hne_t, hremp] using hptr_blue
        have hnext_ne : ¬st.next ptr = th.null_ptr := by
          simpa [hne_t, hremp, hpred] using hptr_next_ne
        have hafter_old := h_free_next_after ptr hptr_block_old hptr_blue_old hnext_ne
        simpa [hne_t, hremp, hpred] using hafter_old
  · intro ptr hptr_block hptr_blue hne_t hptr_next_ne
    by_cases hpred : st.is_block ptr = true ∧ st.color ptr = blue ∧ st.next ptr = t
    · have hptr_blue_old : st.color ptr = blue := by
        simpa [hne_t] using hptr_blue
      have ht_ne_null : t ≠ th.null_ptr := by
        intro ht_null
        have : st.is_block th.null_ptr = true := by
          simpa [ht_null] using ht
        simpa [h_null_not_block] using this
      have hnext_ne_old : ¬st.next ptr = th.null_ptr := by
        intro hnext_eq
        exact ht_ne_null (by simpa [hpred.2.2] using hnext_eq)
      have hafter_old := h_free_next_after ptr hptr_block hptr_blue_old hnext_ne_old
      have hnext_ne : ¬st.next t = th.null_ptr := by
        simpa [hne_t, hpred] using hptr_next_ne
      have hafter_t := h_free_next_after t ht hblue hnext_ne
      have hpos := h_valid_size t ht
      have hle : th.ptrToAddr t ≤ th.ptrToAddr (st.next t) := by
        omega
      have hafter_new : th.ptrToAddr ptr + st.size ptr ≤ th.ptrToAddr (st.next t) := by
        omega
      simpa [hne_t, hpred] using hafter_new
    · have hptr_blue_old : st.color ptr = blue := by
        simpa [hne_t] using hptr_blue
      have hnext_ne : ¬st.next ptr = th.null_ptr := by
        simpa [hne_t, hpred] using hptr_next_ne
      have hafter_old := h_free_next_after ptr hptr_block hptr_blue_old hnext_ne
      simpa [hne_t, hpred] using hafter_old

theorem Allocate_free_next_unique_predecessor (ρ : Type) (σ : Type) (Mutator : Type)
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
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
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
  all_goals simp_all

theorem Allocate_free_blocks_have_list_entry (ρ : Type) (σ : Type) (Mutator : Type)
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
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
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
  intro hphase hreq t ht hblue hlist hsize
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  split
  · by_cases hhead : t = st.free_head
    · simp [hhead]
      intro _ ptr hptr_block hptr_blue
      by_cases hremp : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = ptr
      · left
        exact hremp
      · by_cases htptr : t = ptr
        · subst ptr
          have hcontra : False := by
            have h := hptr_blue
            simp at h
            exact Color_Enum.distinct.2.2.2.2.1 h.symm
          exact hcontra.elim
        · have hptr_block_old : st.is_block ptr = true := hptr_block hremp
          have hptr_blue_old : st.color ptr = blue := by
            simpa [htptr, hremp] using hptr_blue
          have hentry_old := h_free_list_entry (by simpa [hphase]) ptr hptr_block_old hptr_blue_old
          rcases hentry_old with hentry_old | hentry_old
          · have : ptr = t := by simpa [hhead] using hentry_old
            exact (htptr this).elim
          · rcases hentry_old with ⟨pred, hpred_block, hpred_blue, hpred_next⟩
            by_cases hpred_t : pred = t
            · subst pred
              right
              refine ⟨th.addrToPtr (th.ptrToAddr t + ↑reqSize), ?_, ?_, ?_⟩
              · intro hrem
                exact False.elim (hrem rfl)
              · simp
              · simp [hpred_next]
            · right
              refine ⟨pred, ?_, ?_, ?_⟩
              · intro hrem
                exact hpred_block
              · have hpred_blue' : st.color pred = blue := hpred_blue
                simpa [hpred_t, hremp] using hpred_blue'
              · have hpred_next' : st.next pred = ptr := hpred_next
                simpa [hpred_t, hremp] using hpred_next'
    · simp [hhead]
      intro _ ptr hptr_block hptr_blue
      by_cases hremp : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = ptr
      · right
        rcases hlist with hlist | hlist
        · exact (hhead hlist).elim
        · rcases hlist with ⟨pred, hpred_block, hpred_blue, hpred_next⟩
          refine ⟨pred, ?_, ?_, ?_⟩
          · intro _
            exact hpred_block
          · simpa [hremp] using hpred_blue
          · simpa [hremp, hpred_next] using hpred_next
      · by_cases htptr : t = ptr
        · subst ptr
          have hcontra : False := by
            have h := hptr_blue
            simp at h
            exact Color_Enum.distinct.2.2.2.2.1 h.symm
          exact hcontra.elim
        · have hptr_block_old : st.is_block ptr = true := hptr_block hremp
          have hptr_blue_old : st.color ptr = blue := by
            simpa [htptr, hremp] using hptr_blue
          have hentry_old := h_free_list_entry (by simpa [hphase]) ptr hptr_block_old hptr_blue_old
          rcases hentry_old with hentry_old | hentry_old
          · left
            exact hentry_old
          · rcases hentry_old with ⟨pred, hpred_block, hpred_blue, hpred_next⟩
            by_cases hpred_t : pred = t
            · subst pred
              right
              refine ⟨th.addrToPtr (th.ptrToAddr t + ↑reqSize), ?_, ?_, ?_⟩
              · intro hrem
                exact False.elim (hrem rfl)
              · simp
              · simp [hpred_next]
            · right
              refine ⟨pred, ?_, ?_, ?_⟩
              · intro hrem
                exact hpred_block
              · have hpred_blue' : st.color pred = blue := hpred_blue
                simpa [hpred_t, hremp] using hpred_blue'
              · have hpred_next' : st.next pred = ptr := hpred_next
                simpa [hpred_t, hremp] using hpred_next'
  · by_cases hhead : t = st.free_head
    · simp [hhead]
      intro _ ptr hptr_block hptr_blue
      by_cases htptr : t = ptr
      · subst ptr
        have hcontra : False := by
          have h := hptr_blue
          simp at h
          exact Color_Enum.distinct.2.2.2.2.1 h.symm
        exact hcontra.elim
      · have hptr_blue_old : st.color ptr = blue := by
          simpa [htptr] using hptr_blue
        have hentry_old := h_free_list_entry (by simpa [hphase]) ptr hptr_block hptr_blue_old
        rcases hentry_old with hentry_old | hentry_old
        · have : ptr = t := by simpa [hhead] using hentry_old
          exact (htptr this).elim
        · right
          rcases hentry_old with ⟨pred, hpred_block, hpred_blue, hpred_next⟩
          by_cases hpred_t : pred = t
          · subst pred
            have hnext_ne : ¬st.next t = th.null_ptr := by
              intro hnext_null
              have : st.is_block th.null_ptr = true := by
                have hptr_null : ptr = th.null_ptr := by
                  rw [← hpred_next, hnext_null]
                simpa [hptr_null] using hptr_block
              simpa [h_null_not_block] using this
            have hnext := h_free_next_wf t ht hblue hnext_ne
            have hnext_not_t : ¬st.next t = t := by
              intro hself
              have hafter := h_free_next_after t ht hblue hnext_ne
              have hafter' : th.ptrToAddr t + st.size t ≤ th.ptrToAddr t := by
                simpa [hself] using hafter
              have hpos := h_valid_size t ht
              omega
            have ht_next : ¬t = st.next t := by
              intro h
              exact hnext_not_t h.symm
            refine ⟨st.next t, ?_, ?_, ?_⟩
            · exact hnext.1
            · simpa [ht_next] using hnext.2
            · simpa [ht_next, hpred_next]
          · have hpred_next_not_t : ¬st.next pred = t := by
              intro hnext_t
              exact htptr (by rw [← hpred_next, hnext_t])
            refine ⟨pred, hpred_block, ?_, ?_⟩
            · simpa [hpred_t] using hpred_blue
            · simpa [hpred_t, hpred_next_not_t] using hpred_next
    · simp [hhead]
      intro _ ptr hptr_block hptr_blue
      by_cases htptr : t = ptr
      · subst ptr
        have hcontra : False := by
          have h := hptr_blue
          simp at h
          exact Color_Enum.distinct.2.2.2.2.1 h.symm
        exact hcontra.elim
      · have hptr_blue_old : st.color ptr = blue := by
          simpa [htptr] using hptr_blue
        have hentry_old := h_free_list_entry (by simpa [hphase]) ptr hptr_block hptr_blue_old
        rcases hentry_old with hentry_old | hentry_old
        · left
          exact hentry_old
        · right
          rcases hentry_old with ⟨pred, hpred_block, hpred_blue, hpred_next⟩
          by_cases hpred_t : pred = t
          · subst pred
            have hnext_ne : ¬st.next t = th.null_ptr := by
              intro hnext_null
              have : st.is_block th.null_ptr = true := by
                have hptr_null : ptr = th.null_ptr := by
                  rw [← hpred_next, hnext_null]
                simpa [hptr_null] using hptr_block
              simpa [h_null_not_block] using this
            have hnext := h_free_next_wf t ht hblue hnext_ne
            have hnext_not_t : ¬st.next t = t := by
              intro hself
              have hafter := h_free_next_after t ht hblue hnext_ne
              have hafter' : th.ptrToAddr t + st.size t ≤ th.ptrToAddr t := by
                simpa [hself] using hafter
              have hpos := h_valid_size t ht
              omega
            have ht_next : ¬t = st.next t := by
              intro h
              exact hnext_not_t h.symm
            refine ⟨st.next t, ?_, ?_, ?_⟩
            · exact hnext.1
            · simpa [ht_next] using hnext.2
            · simpa [ht_next, hpred_next]
          · refine ⟨pred, hpred_block, ?_, ?_⟩
            · simpa [hpred_t] using hpred_blue
            · have hpred_next_not_t : ¬st.next pred = t := by
                intro hnext_t
                exact htptr (by rw [← hpred_next, hnext_t])
              simpa [hpred_t, hpred_next_not_t] using hpred_next

theorem Allocate_allocated_block_next_unused (ρ : Type) (σ : Type) (Mutator : Type)
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
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@allocated_block_next_unused ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hphase hreq t ht hblue hlist hsize
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  split
  · intro ptr hptr_block hptr_not_blue hne_t
    by_cases hrem : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = ptr
    · subst ptr
      exact False.elim (hptr_not_blue (by simp [hne_t]))
    · have hptr_block_old : st.is_block ptr = true := hptr_block hrem
      have hptr_not_blue_old : ¬st.color ptr = blue := by
        simpa [hne_t, hrem] using hptr_not_blue
      have hnext_old := h_alloc_next_unused ptr hptr_block_old hptr_not_blue_old
      by_cases hpred : st.is_block ptr = true ∧ st.color ptr = blue ∧ st.next ptr = t
      · exact False.elim (hptr_not_blue_old hpred.2.1)
      · simpa [hrem, hpred] using hnext_old
  · intro ptr hptr_block hptr_not_blue hne_t
    have hptr_not_blue_old : ¬st.color ptr = blue := by
      simpa [hne_t] using hptr_not_blue
    have hnext_old := h_alloc_next_unused ptr hptr_block hptr_not_blue_old
    by_cases hpred : st.is_block ptr = true ∧ st.color ptr = blue ∧ st.next ptr = t
    · exact False.elim (hptr_not_blue_old hpred.2.1)
    · simpa [hpred] using hnext_old

theorem Allocate_allocated_white_before_coloring (ρ : Type) (σ : Type) (Mutator : Type)
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
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@allocated_white_before_coloring ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  intro hphase hreq t ht hblue hlist hsize
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  split
  · intro p hp_phase hp_block hp_not_blue hne_t
    by_cases hrem : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = p
    · exact False.elim (hp_not_blue (by simp [hne_t, hrem]))
    · have hp_block_old : st.is_block p = true := hp_block hrem
      have hp_not_blue_old : ¬st.color p = blue := by
        simpa [hne_t, hrem] using hp_not_blue
      simpa [hrem] using h_white_before p hp_phase hp_block_old hp_not_blue_old
  · intro p hp_phase hp_block hp_not_blue hne_t
    have hp_not_blue_old : ¬st.color p = blue := by
      simpa [hne_t] using hp_not_blue
    exact h_white_before p hp_phase hp_block hp_not_blue_old

theorem Allocate_blue_never_child_outside_sweep (ρ : Type) (σ : Type) (Mutator : Type)
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
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
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
  intro hphase hreq t ht hblue hlist hsize
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  split
  · intro off p hnotSweep hp_block hp_blue parent hparent_block hparent_not_rem hparent_not_t
    by_cases hpt : t = p
    · subst p
      exact h_blue_no_child off t (by simpa [hphase] using hnotSweep) ht hblue parent (hparent_block hparent_not_t)
    · by_cases hremp : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = p
      · subst p
        by_cases hfield : st.field parent off (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) = true
        · have hrem_alloc := h_fields_to off parent (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) (by simpa [hphase] using hnotSweep) hfield
          have ht_lt_rem : th.ptrToAddr t < th.ptrToAddr (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) := by
            rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
            omega
          have hoverlap := h_no_overlap t (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) ht hrem_alloc.1 ht_lt_rem
          rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hoverlap
          omega
        · simpa using hfield
      · have hp_block_old : st.is_block p = true := hp_block hremp
        have hp_blue_old : st.color p = blue := by
          simpa [hpt, hremp] using hp_blue
        exact h_blue_no_child off p (by simpa [hphase] using hnotSweep) hp_block_old hp_blue_old parent (hparent_block hparent_not_t)
  · intro off p hnotSweep hp_block hp_blue parent hparent_block hparent_not_t
    by_cases hpt : t = p
    · subst p
      exact h_blue_no_child off t (by simpa [hphase] using hnotSweep) ht hblue parent hparent_block
    · have hp_blue_old : st.color p = blue := by
        simpa [hpt] using hp_blue
      exact h_blue_no_child off p (by simpa [hphase] using hnotSweep) hp_block hp_blue_old parent hparent_block

theorem Allocate_blue_never_parent (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ]
    [Allocate_dec_0 :
      delta% @VerifiedGc.Allocate._veil_dec_type_0 χ Ptr Mutator Collector HeapSize Color Phase χ_rep Color_Enum] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub Allocate_dec_0 _m reqSize)
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
  intro hphase hreq t ht hblue hlist hsize
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  split
  · intro off p hp_block hp_blue child hchild_block hne_t hne_rem
    by_cases hpt : t = p
    · subst p
      have hcontra : False := by
        have h : white = blue := by
          simpa [hne_t] using hp_blue
        exact Color_Enum.distinct.2.2.2.2.1 h.symm
      exact hcontra.elim
    · by_cases hremp : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = p
      · subst p
        by_cases hfield : st.field (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) off child = true
        · have hrem_from := h_fields_from off (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) child hfield
          have ht_lt_rem : th.ptrToAddr t < th.ptrToAddr (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) := by
            rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
            omega
          have hoverlap := h_no_overlap t (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) ht hrem_from.1 ht_lt_rem
          rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hoverlap
          omega
        · simpa using hfield
      · have hp_block_old : st.is_block p = true := hp_block hremp
        have hp_blue_old : st.color p = blue := by
          simpa [hpt, hremp] using hp_blue
        by_cases hremc : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = child
        · subst child
          by_cases hfield : st.field p off (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) = true
          · have hrem_to :=
              h_fields_to off p (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) (by
                intro hs
                rw [hphase] at hs
                exact Phase_Enum.distinct.2.2.2.2.2.1 hs) hfield
            have ht_lt_rem : th.ptrToAddr t < th.ptrToAddr (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) := by
              rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
              omega
            have hoverlap :=
              h_no_overlap t (th.addrToPtr (th.ptrToAddr t + ↑reqSize)) ht hrem_to.1 ht_lt_rem
            rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hoverlap
            omega
          · simpa using hfield
        · exact h_blue_no_parent off p hp_block_old hp_blue_old child (hchild_block hremc)
  · intro off p hp_block hp_blue child hchild_block hne_t
    by_cases hpt : t = p
    · subst p
      exact h_blue_no_parent off t ht hblue child hchild_block
    · have hp_blue_old : st.color p = blue := by
        simpa [hpt] using hp_blue
      exact h_blue_no_parent off p hp_block hp_blue_old child hchild_block
