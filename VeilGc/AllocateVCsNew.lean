import Veil
import VeilGc
import Mathlib.Tactic.CasesM

open VerifiedGc
open VerifiedGc.Color_EnumClass

set_option maxHeartbeats 0
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  classical
  intro hphase hreq t ht ht_blue hsize_le
  let rem := th.addrToPtr (th.ptrToAddr t + ↑reqSize)
  by_cases hsplit : ↑reqSize < st.size t
  · by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hrem_heap : th.ptrToAddr th.heap_start ≤ th.ptrToAddr rem ∧
          th.ptrToAddr rem < th.ptrToAddr th.heap_start + HeapSize := by
        have ht_heap := hinv.2.1 t ht
        have ht_fits := hinv.2.2.2.1 t ht
        constructor
        · dsimp [rem]
          rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
          omega
        · dsimp [rem]
          rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
          omega
      simp [hhead, hsplit_head]
      intro ptr hptr
      by_cases hptr_rem : rem = ptr
      · subst ptr
        exact hrem_heap
      · exact hinv.2.1 ptr (hptr (by
          intro hptr_rem_head
          exact hptr_rem (by
            dsimp [rem]
            simpa [hhead] using hptr_rem_head)))
    · simp [hsplit, hhead]
      have hrem_heap : th.ptrToAddr th.heap_start ≤ th.ptrToAddr rem ∧
          th.ptrToAddr rem < th.ptrToAddr th.heap_start + HeapSize := by
        have ht_heap := hinv.2.1 t ht
        have ht_fits := hinv.2.2.2.1 t ht
        constructor
        · dsimp [rem]
          rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
          omega
        · dsimp [rem]
          rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
          omega
      intro pred hpred_block hpred_blue hpred_next ptr hptr
      by_cases hptr_rem : rem = ptr
      · subst ptr
        exact hrem_heap
      · exact hinv.2.1 ptr (hptr hptr_rem)
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hnosplit_head]
      intro ptr hptr
      exact hinv.2.1 ptr hptr
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next ptr hptr
      exact hinv.2.1 ptr hptr

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  classical
  intro hphase hreq t ht ht_blue hsize_le
  let rem := th.addrToPtr (th.ptrToAddr t + ↑reqSize)
  have hnull_not_block : st.is_block th.null_ptr = false := hinv.2.2.1
  by_cases hsplit : ↑reqSize < st.size t
  · have hrem_not_null : ¬rem = th.null_ptr := by
      intro hrem_null
      have ht_heap := hinv.2.1 t ht
      have ht_fits := hinv.2.2.2.1 t ht
      have haddr : th.ptrToAddr t + ↑reqSize = th.ptrToAddr th.null_ptr := by
        have hcongr := congrArg th.ptrToAddr hrem_null
        dsimp [rem] at hcongr
        rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hcongr
        exact hcongr
      have hnull_lower : th.ptrToAddr th.heap_start ≤ th.ptrToAddr th.null_ptr := by
        rw [← haddr]
        omega
      have hnull_out := has.2.2.2.2 hnull_lower
      omega
    by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      simp [hhead, hsplit_head]
      constructor
      · intro hrem_null_head
        exact hrem_not_null (by
          dsimp [rem]
          simpa [hhead] using hrem_null_head)
      · exact hnull_not_block
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next
      exact ⟨hrem_not_null, hnull_not_block⟩
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hnosplit_head]
      exact hnull_not_block
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next
      exact hnull_not_block

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  intro hphase hreq t ht ht_blue hsize_le
  let rem := th.addrToPtr (th.ptrToAddr t + ↑reqSize)
  have ht_fits := hinv.2.2.2.1 t ht
  by_cases hsplit : ↑reqSize < st.size t
  · have hrem_addr : th.ptrToAddr rem = th.ptrToAddr t + ↑reqSize := by
      dsimp [rem]
      rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
    by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hsize_le_head : ↑reqSize ≤ st.size st.free_head := by
        simpa [hhead] using hsize_le
      have ht_fits_head :
          th.ptrToAddr st.free_head + st.size st.free_head ≤ th.ptrToAddr th.heap_start + HeapSize := by
        simpa [hhead] using ht_fits
      have hrem_addr_head : th.ptrToAddr rem = th.ptrToAddr st.free_head + ↑reqSize := by
        simpa [hhead] using hrem_addr
      simp [hhead, hsplit_head]
      intro ptr hptr
      by_cases hptr_t : t = ptr
      · subst ptr
        simp
        omega
      · by_cases hptr_rem : rem = ptr
        · subst ptr
          simp [rem, hrem_addr_head, hptr_t]
          omega
        · have hptr_old : st.is_block ptr = true := hptr (by
            intro h
            exact hptr_rem (by
              dsimp [rem]
              simpa [hhead] using h))
          simpa [hptr_t, hptr_rem, rem] using hinv.2.2.2.1 ptr hptr_old
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next ptr hptr
      by_cases hptr_t : t = ptr
      · subst ptr
        simp
        omega
      · by_cases hptr_rem : rem = ptr
        · subst ptr
          simp [rem, hrem_addr, hptr_t]
          omega
        · have hptr_old : st.is_block ptr = true := hptr hptr_rem
          simpa [hptr_t, hptr_rem, rem] using hinv.2.2.2.1 ptr hptr_old
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hnosplit_head]
      intro ptr hptr
      by_cases hptr_t : t = ptr
      · subst ptr
        simp
        omega
      · simpa [hptr_t] using hinv.2.2.2.1 ptr hptr
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next ptr hptr
      by_cases hptr_t : t = ptr
      · subst ptr
        simp
        omega
      · simpa [hptr_t] using hinv.2.2.2.1 ptr hptr

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  classical
  intro hphase hreq t ht ht_blue hsize_le
  let rem := th.addrToPtr (th.ptrToAddr t + ↑reqSize)
  have hrem_addr : th.ptrToAddr rem = th.ptrToAddr t + ↑reqSize := by
    dsimp [rem]
    rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
  have ptr_addr_inj : ∀ {a b : Ptr}, th.ptrToAddr a = th.ptrToAddr b → a = b := by
    intro a b haddr
    have h := congrArg th.addrToPtr haddr
    simpa [has.2.1 a, has.2.1 b] using h
  by_cases hsplit : ↑reqSize < st.size t
  · by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      have hrem_addr_head : th.ptrToAddr rem = th.ptrToAddr st.free_head + ↑reqSize := by
        simpa [hhead] using hrem_addr
      simp [hhead, hsplit_head]
      intro p q hp hq hpq
      by_cases hp_t : t = p
      · subst p
        by_cases hq_rem : rem = q
        · subst q
          simp [rem, hrem_addr_head, hfree_t]
        · have hq_old : st.is_block q = true := hq (by
            intro hq_rem_head
            exact hq_rem (by
              dsimp [rem]
              simpa [hhead] using hq_rem_head))
          have hold := hinv.2.2.2.2.1 t q ht hq_old hpq
          simp [hfree_t]
          omega
      · by_cases hp_rem : rem = p
        · subst p
          by_cases hq_rem : rem = q
          · subst q
            rw [hrem_addr] at hpq
            omega
          · have hq_old : st.is_block q = true := hq (by
              intro hq_rem_head
              exact hq_rem (by
                dsimp [rem]
                simpa [hhead] using hq_rem_head))
            have ht_lt_q : th.ptrToAddr t < th.ptrToAddr q := by
              rw [hrem_addr] at hpq
              omega
            have hold := hinv.2.2.2.2.1 t q ht hq_old ht_lt_q
            have ht_not_raw : ¬t = th.addrToPtr (th.ptrToAddr t + ↑reqSize) := by
              simpa [rem] using hp_t
            have hraw_rem : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = rem := by
              dsimp [rem]
            have hfree_not_rem : ¬st.free_head = rem := by
              simpa [hhead] using hp_t
            have hraw_head_rem :
                th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize) = rem := by
              dsimp [rem]
              simpa [hhead]
            have hrem_size :
                (if st.free_head = rem then ↑reqSize
                 else if th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize) = rem then
                   st.size st.free_head - ↑reqSize
                 else st.size rem) = st.size st.free_head - ↑reqSize := by
              simp [hfree_not_rem, hraw_head_rem]
            rw [hrem_size]
            rw [hrem_addr_head]
            rw [hhead] at hold
            omega
        · have hp_old : st.is_block p = true := hp (by
            intro hp_rem_head
            exact hp_rem (by
              dsimp [rem]
              simpa [hhead] using hp_rem_head))
          by_cases hq_rem : rem = q
          · subst q
            have hp_ne_t : ¬p = t := by
              intro h
              exact hp_t h.symm
            have hp_not_raw : ¬th.addrToPtr (th.ptrToAddr t + ↑reqSize) = p := by
              simpa [rem] using hp_rem
            have hp_free : ¬st.free_head = p := by
              simpa [hhead] using hp_t
            have hp_not_raw_head : ¬th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize) = p := by
              simpa [hhead] using hp_not_raw
            simp only [hp_free, hp_not_raw_head, if_false]
            rw [hrem_addr_head] at hpq ⊢
            by_cases hp_before_t : th.ptrToAddr p < th.ptrToAddr t
            · have hold := hinv.2.2.2.2.1 p t hp_old ht hp_before_t
              omega
            · have hp_addr_ne : th.ptrToAddr p ≠ th.ptrToAddr t := by
                intro haddr
                exact hp_ne_t (ptr_addr_inj haddr)
              have ht_before_p : th.ptrToAddr t < th.ptrToAddr p := by
                omega
              have hold := hinv.2.2.2.2.1 t p ht hp_old ht_before_p
              omega
          · have hq_old : st.is_block q = true := hq (by
              intro hq_rem_head
              exact hq_rem (by
                dsimp [rem]
                simpa [hhead] using hq_rem_head))
            have hp_ne_t : ¬p = t := by
              intro h
              exact hp_t h.symm
            have hp_not_raw : ¬th.addrToPtr (th.ptrToAddr t + ↑reqSize) = p := by
              simpa [rem] using hp_rem
            have hp_free : ¬st.free_head = p := by
              simpa [hhead] using hp_t
            have hp_not_raw_head : ¬th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize) = p := by
              simpa [hhead] using hp_not_raw
            simpa only [hp_free, hp_not_raw_head, if_false] using hinv.2.2.2.2.1 p q hp_old hq_old hpq
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next p q hp hq hpq
      by_cases hp_t : t = p
      · subst p
        by_cases hq_rem : rem = q
        · subst q
          simp [rem, hrem_addr]
        · have hq_old : st.is_block q = true := hq hq_rem
          have hold := hinv.2.2.2.2.1 t q ht hq_old hpq
          simp
          omega
      · by_cases hp_rem : rem = p
        · subst p
          by_cases hq_rem : rem = q
          · subst q
            rw [hrem_addr] at hpq
            omega
          · have hq_old : st.is_block q = true := hq hq_rem
            have ht_lt_q : th.ptrToAddr t < th.ptrToAddr q := by
              rw [hrem_addr] at hpq
              omega
            have hold := hinv.2.2.2.2.1 t q ht hq_old ht_lt_q
            have ht_not_raw : ¬t = th.addrToPtr (th.ptrToAddr t + ↑reqSize) := by
              simpa [rem] using hp_t
            have hraw_rem : th.addrToPtr (th.ptrToAddr t + ↑reqSize) = rem := by
              dsimp [rem]
            have hrem_size :
                (if t = rem then ↑reqSize
                 else if th.addrToPtr (th.ptrToAddr t + ↑reqSize) = rem then st.size t - ↑reqSize
                 else st.size rem) = st.size t - ↑reqSize := by
              simp [hp_t, hraw_rem]
            rw [hrem_size]
            rw [hrem_addr]
            omega
        · have hp_old : st.is_block p = true := hp hp_rem
          by_cases hq_rem : rem = q
          · subst q
            have hp_ne_t : ¬p = t := by
              intro h
              exact hp_t h.symm
            have hp_not_raw : ¬th.addrToPtr (th.ptrToAddr t + ↑reqSize) = p := by
              simpa [rem] using hp_rem
            simp only [hp_t, hp_not_raw, if_false]
            rw [hrem_addr] at hpq ⊢
            by_cases hp_before_t : th.ptrToAddr p < th.ptrToAddr t
            · have hold := hinv.2.2.2.2.1 p t hp_old ht hp_before_t
              omega
            · have hp_addr_ne : th.ptrToAddr p ≠ th.ptrToAddr t := by
                intro haddr
                exact hp_ne_t (ptr_addr_inj haddr)
              have ht_before_p : th.ptrToAddr t < th.ptrToAddr p := by
                omega
              have hold := hinv.2.2.2.2.1 t p ht hp_old ht_before_p
              omega
          · have hq_old : st.is_block q = true := hq hq_rem
            have hp_ne_t : ¬p = t := by
              intro h
              exact hp_t h.symm
            have hp_not_raw : ¬th.addrToPtr (th.ptrToAddr t + ↑reqSize) = p := by
              simpa [rem] using hp_rem
            simpa only [hp_t, hp_not_raw, if_false] using hinv.2.2.2.2.1 p q hp_old hq_old hpq
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      simp [hhead, hnosplit_head]
      intro p q hp hq hpq
      by_cases hp_t : t = p
      · subst p
        simp [hfree_t]
        have hold := hinv.2.2.2.2.1 t q ht hq hpq
        omega
      · have hp_ne_t : ¬p = t := by
          intro h
          exact hp_t h.symm
        have hp_free : ¬st.free_head = p := by
          simpa [hhead] using hp_t
        simpa [hp_free] using hinv.2.2.2.2.1 p q hp hq hpq
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next p q hp hq hpq
      by_cases hp_t : t = p
      · subst p
        simp
        have hold := hinv.2.2.2.2.1 t q ht hq hpq
        omega
      · have hp_ne_t : ¬p = t := by
          intro h
          exact hp_t h.symm
        simpa [hp_t] using hinv.2.2.2.2.1 p q hp hq hpq

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  classical
  intro hphase hreq t ht ht_blue hsize_le
  let rem := th.addrToPtr (th.ptrToAddr t + ↑reqSize)
  by_cases hsplit : ↑reqSize < st.size t
  · by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      simp [hhead, hsplit_head]
      intro p hp
      by_cases htp : t = p
      · subst p
        right
        simp [hfree_t]
      · by_cases hrp : th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize) = p
        · have htp' : ¬ t = p := htp
          subst p
          have ht_not_raw : ¬t = th.addrToPtr (th.ptrToAddr t + ↑reqSize) := by
            intro h
            have haddr := congrArg th.ptrToAddr h
            rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at haddr
            omega
          have hold := hinv.2.2.2.2.2.1 t ht
          rcases hold with hold | hold
          · left
            simp [hfree_t, ht_not_raw, has.2.2.2.1]
            omega
          · right
            intro hnew
            simp [hfree_t, ht_not_raw, has.2.2.2.1]
            have haddr : th.ptrToAddr t + ↑reqSize + (st.size t - ↑reqSize) =
                th.ptrToAddr t + st.size t := by
              omega
            have hptr : th.addrToPtr (th.ptrToAddr t + ↑reqSize + (st.size t - ↑reqSize)) =
                th.addrToPtr (th.ptrToAddr t + st.size t) := by
              rw [haddr]
            simpa [hptr] using hold
        · have hp_old : st.is_block p = true := hp hrp
          have hfree_not_p : ¬st.free_head = p := by
            simpa [hhead] using htp
          have hold := hinv.2.2.2.2.2.1 p hp_old
          rcases hold with hold | hold
          · left
            simpa [hfree_not_p, hrp] using hold
          · right
            intro _
            simpa [hfree_not_p, hrp] using hold
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next p hp
      by_cases htp : t = p
      · subst p
        right
        simp
      · by_cases hrp : rem = p
        · subst p
          have hold := hinv.2.2.2.2.2.1 t ht
          have htp' : ¬ t = rem := by
            simpa using htp
          rcases hold with hold | hold
          · left
            simp [rem, htp', has.2.2.2.1]
            omega
          · right
            intro hnew
            simp [rem, htp', has.2.2.2.1]
            have haddr : th.ptrToAddr t + ↑reqSize + (st.size t - ↑reqSize) =
                th.ptrToAddr t + st.size t := by
              omega
            have hptr : th.addrToPtr (th.ptrToAddr t + ↑reqSize + (st.size t - ↑reqSize)) =
                th.addrToPtr (th.ptrToAddr t + st.size t) := by
              rw [haddr]
            rwa [hptr]
        · have hp_old := hp hrp
          have hold := hinv.2.2.2.2.2.1 p hp_old
          rcases hold with hold | hold
          · left
            simpa [htp, hrp, rem] using hold
          · right
            intro _
            simpa [htp, hrp, rem] using hold
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      simp [hhead, hnosplit_head]
      intro p hp
      by_cases htp : t = p
      · subst p
        have hold := hinv.2.2.2.2.2.1 t ht
        rcases hold with hold | hold
        · left
          simp [hfree_t]
          omega
        · right
          simp [hfree_t]
          have haddr : th.ptrToAddr t + ↑reqSize = th.ptrToAddr t + st.size t := by
            omega
          simpa [haddr] using hold
      · have hfree_not_p : ¬st.free_head = p := by
          simpa [hhead] using htp
        have hold := hinv.2.2.2.2.2.1 p hp
        simpa [hfree_not_p] using hold
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next p hp
      by_cases htp : t = p
      · subst p
        have hold := hinv.2.2.2.2.2.1 t ht
        rcases hold with hold | hold
        · left
          simp
          omega
        · right
          simp
          have haddr : th.ptrToAddr t + ↑reqSize = th.ptrToAddr t + st.size t := by
            omega
          simpa [haddr] using hold
      · have hold := hinv.2.2.2.2.2.1 p hp
        simpa [htp] using hold

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  classical
  intro hphase hreq t ht ht_blue hsize_le
  let rem := th.addrToPtr (th.ptrToAddr t + ↑reqSize)
  by_cases hsplit : ↑reqSize < st.size t
  · by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      simp [hhead, hsplit_head]
      intro ptr hptr
      by_cases hptr_t : t = ptr
      · subst ptr
        simpa [hfree_t] using hreq
      · by_cases hptr_rem_head : th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize) = ptr
        · have hfree_not_ptr : ¬st.free_head = ptr := by
            intro hfree_ptr
            have haddr := congrArg th.ptrToAddr hfree_ptr
            rw [← hptr_rem_head] at haddr
            rw [has.2.2.2.1 (th.ptrToAddr st.free_head + ↑reqSize)] at haddr
            omega
          simp [hfree_not_ptr, hptr_rem_head]
          omega
        · have hptr_old : st.is_block ptr = true := hptr hptr_rem_head
          have hptr_rem : ¬rem = ptr := by
            intro h
            exact hptr_rem_head (by
              dsimp [rem] at h
              simpa [hhead] using h)
          have hptr_free : ¬st.free_head = ptr := by
            simpa [hhead] using hptr_t
          simpa [hptr_free, hptr_rem_head] using hinv.2.2.2.2.2.2.1 ptr hptr_old
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next ptr hptr
      by_cases hptr_t : t = ptr
      · subst ptr
        simp
        exact hreq
      · by_cases hptr_rem : rem = ptr
        · simp [rem, hptr_t, hptr_rem]
          omega
        · have hptr_old : st.is_block ptr = true := hptr hptr_rem
          simpa [hptr_t, hptr_rem, rem] using hinv.2.2.2.2.2.2.1 ptr hptr_old
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      simp [hhead, hnosplit_head]
      intro ptr hptr
      by_cases hptr_t : t = ptr
      · subst ptr
        simpa [hfree_t] using hreq
      · have hptr_free : ¬st.free_head = ptr := by
          simpa [hhead] using hptr_t
        simpa [hptr_free] using hinv.2.2.2.2.2.2.1 ptr hptr
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next ptr hptr
      by_cases hptr_t : t = ptr
      · subst ptr
        simpa using hreq
      · simpa [hptr_t] using hinv.2.2.2.2.2.2.1 ptr hptr

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  intro hphase hreq t ht ht_blue hsize_le
  let rem := th.addrToPtr (th.ptrToAddr t + ↑reqSize)
  by_cases hsplit : ↑reqSize < st.size t
  · by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      simp [hhead, hsplit_head]
      intro ptr hptr
      by_cases hptr_t : t = ptr
      · subst ptr
        intro h
        have hw : white = uncolored := by
          simpa [hfree_t] using h
        exact Color_Enum.distinct.2.1 hw.symm
      · by_cases hptr_rem_head : th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize) = ptr
        · have hfree_not_ptr : ¬st.free_head = ptr := by
            simpa [hhead] using hptr_t
          simp [hfree_not_ptr, hptr_rem_head]
          exact fun h => Color_Enum.distinct.1 h.symm
        · have hptr_old : st.is_block ptr = true := hptr hptr_rem_head
          have hptr_free : ¬st.free_head = ptr := by
            simpa [hhead] using hptr_t
          simpa [hptr_free, hptr_rem_head] using hinv.2.2.2.2.2.2.2.1 ptr hptr_old
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next ptr hptr
      by_cases hptr_t : t = ptr
      · subst ptr
        intro h
        have hw : white = uncolored := by
          simpa using h
        exact Color_Enum.distinct.2.1 hw.symm
      · by_cases hptr_rem : rem = ptr
        · simp [rem, hptr_t, hptr_rem]
          exact fun h => Color_Enum.distinct.1 h.symm
        · have hptr_old : st.is_block ptr = true := hptr hptr_rem
          simpa [hptr_t, hptr_rem, rem] using hinv.2.2.2.2.2.2.2.1 ptr hptr_old
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      simp [hhead, hnosplit_head]
      intro ptr hptr
      by_cases hptr_t : t = ptr
      · subst ptr
        intro h
        have hw : white = uncolored := by
          simpa [hfree_t] using h
        exact Color_Enum.distinct.2.1 hw.symm
      · have hptr_free : ¬st.free_head = ptr := by
          simpa [hhead] using hptr_t
        simpa [hptr_free] using hinv.2.2.2.2.2.2.2.1 ptr hptr
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next ptr hptr
      by_cases hptr_t : t = ptr
      · subst ptr
        intro h
        exact Color_Enum.distinct.2.1 (by simpa [hhead] using h.symm)
      · simpa [hptr_t] using hinv.2.2.2.2.2.2.2.1 ptr hptr



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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  intro hphase hreq t ht ht_blue hsize_le
  let rem := th.addrToPtr (th.ptrToAddr t + ↑reqSize)
  by_cases hsplit : ↑reqSize < st.size t
  · by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      simp [hhead, hsplit_head]
      intro ptr hroot
      by_cases hptr_t : t = ptr
      · subst ptr
        constructor
        · intro _
          exact ht
        · intro h
          exact Color_Enum.distinct.2.2.2.2.1 (by simpa [hfree_t] using h.symm)
      · by_cases hptr_rem_head : th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize) = ptr
        · subst ptr
          have hroot_old := hinv.2.2.2.2.2.2.2.2.1 (th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize)) hroot
          have ht_lt_rem : th.ptrToAddr t < th.ptrToAddr (th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize)) := by
            rw [has.2.2.2.1 (th.ptrToAddr st.free_head + ↑reqSize)]
            rw [hfree_t]
            omega
          have hoverlap := hinv.2.2.2.2.1 t (th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize)) ht hroot_old.1 ht_lt_rem
          rw [has.2.2.2.1 (th.ptrToAddr st.free_head + ↑reqSize)] at hoverlap
          rw [hfree_t] at hoverlap
          omega
        · have hroot_old := hinv.2.2.2.2.2.2.2.2.1 ptr hroot
          have hptr_free : ¬st.free_head = ptr := by
            simpa [hhead] using hptr_t
          constructor
          · intro _
            exact hroot_old.1
          · simpa [hptr_free, hptr_rem_head] using hroot_old.2
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next ptr hroot
      by_cases hptr_t : t = ptr
      · subst ptr
        constructor
        · intro _
          exact ht
        · intro h
          exact Color_Enum.distinct.2.2.2.2.1 (by simpa using h.symm)
      · by_cases hptr_rem : rem = ptr
        · subst ptr
          have hroot_old := hinv.2.2.2.2.2.2.2.2.1 rem hroot
          have ht_lt_rem : th.ptrToAddr t < th.ptrToAddr rem := by
            dsimp [rem]
            rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
            omega
          have hoverlap := hinv.2.2.2.2.1 t rem ht hroot_old.1 ht_lt_rem
          dsimp [rem] at hoverlap
          rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hoverlap
          omega
        · have hroot_old := hinv.2.2.2.2.2.2.2.2.1 ptr hroot
          constructor
          · intro _
            exact hroot_old.1
          · simpa [hptr_t, hptr_rem, rem] using hroot_old.2
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      simp [hhead, hnosplit_head]
      intro ptr hroot
      by_cases hptr_t : t = ptr
      · subst ptr
        constructor
        · exact ht
        · intro h
          exact Color_Enum.distinct.2.2.2.2.1 (by simpa [hfree_t] using h.symm)
      · have hroot_old := hinv.2.2.2.2.2.2.2.2.1 ptr hroot
        have hptr_free : ¬st.free_head = ptr := by
          simpa [hhead] using hptr_t
        constructor
        · exact hroot_old.1
        · simpa [hptr_free] using hroot_old.2
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next ptr hroot
      by_cases hptr_t : t = ptr
      · subst ptr
        constructor
        · exact ht
        · intro h
          exact Color_Enum.distinct.2.2.2.2.1 (by simpa using h.symm)
      · have hroot_old := hinv.2.2.2.2.2.2.2.2.1 ptr hroot
        constructor
        · exact hroot_old.1
        · simpa [hptr_t] using hroot_old.2

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  intro hphase hreq t ht ht_blue hsize_le
  by_cases hsplit : ↑reqSize < st.size t
  · by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hsplit_head]
      intro off parent child hne_t hne_rem hfield
      have hfield_old := hinv.2.2.2.2.2.2.2.2.2.1 off parent child hfield
      constructor
      · intro _
        exact hfield_old.1
      · simpa [hne_t, hne_rem] using hfield_old.2
    · simp [hsplit, hhead]
      intro off pred hpred_block hpred_blue hpred_next parent child hne_t hne_rem hfield
      have hfield_old := hinv.2.2.2.2.2.2.2.2.2.1 off parent child hfield
      constructor
      · intro _
        exact hfield_old.1
      · simpa [hne_t, hne_rem] using hfield_old.2
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hnosplit_head]
      intro off parent child hne_t hfield
      have hfield_old := hinv.2.2.2.2.2.2.2.2.2.1 off parent child hfield
      constructor
      · exact hfield_old.1
      · simpa [hne_t] using hfield_old.2
    · simp [hsplit, hhead]
      intro off pred hpred_block hpred_blue hpred_next parent child hne_t hfield
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  intro hphase hreq t ht ht_blue hsize_le
  by_cases hsplit : ↑reqSize < st.size t
  · by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hsplit_head]
      intro off parent child hnotSweep hne_parent_t hne_parent_rem hfield
      have hfield_old := hinv.2.2.2.2.2.2.2.2.2.2.1 off parent child hnotSweep hfield
      constructor
      · intro _
        exact hfield_old.1
      · by_cases htc : t = child
        · subst child
          exact False.elim (hfield_old.2 ht_blue)
        · by_cases hremc : th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize) = child
          · subst child
            have hrem_block := hfield_old.1
            have ht_lt_rem : th.ptrToAddr t < th.ptrToAddr (th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize)) := by
              rw [has.2.2.2.1 (th.ptrToAddr st.free_head + ↑reqSize)]
              rw [← hhead]
              omega
            have hoverlap := hinv.2.2.2.2.1 t (th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize)) ht hrem_block ht_lt_rem
            rw [has.2.2.2.1 (th.ptrToAddr st.free_head + ↑reqSize)] at hoverlap
            rw [← hhead] at hoverlap
            omega
          · have hfree_child : ¬st.free_head = child := by
              simpa [hhead] using htc
            simpa [hfree_child, htc, hremc] using hfield_old.2
    · simp [hsplit, hhead]
      intro off pred hpred_block hpred_blue hpred_next parent child hnotSweep hne_parent_t hne_parent_rem hfield
      have hfield_old := hinv.2.2.2.2.2.2.2.2.2.2.1 off parent child hnotSweep hfield
      constructor
      · intro _
        exact hfield_old.1
      · by_cases htc : t = child
        · subst child
          exact False.elim (hfield_old.2 ht_blue)
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
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hnosplit_head]
      intro off parent child hnotSweep hne_parent_t hfield
      have hfield_old := hinv.2.2.2.2.2.2.2.2.2.2.1 off parent child hnotSweep hfield
      constructor
      · exact hfield_old.1
      · by_cases htc : t = child
        · subst child
          exact False.elim (hfield_old.2 ht_blue)
        · have hfree_child : ¬st.free_head = child := by
            simpa [hhead] using htc
          simpa [hfree_child, htc] using hfield_old.2
    · simp [hsplit, hhead]
      intro off pred hpred_block hpred_blue hpred_next parent child hnotSweep hne_parent_t hfield
      have hfield_old := hinv.2.2.2.2.2.2.2.2.2.2.1 off parent child hnotSweep hfield
      constructor
      · exact hfield_old.1
      · by_cases htc : t = child
        · subst child
          exact False.elim (hfield_old.2 ht_blue)
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  intro hphase hreq t ht ht_blue hsize_le
  by_cases hsplit : ↑reqSize < st.size t
  · by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hsplit_head]
      intro off parent child hparent_block hparent_blue hne_t hne_rem
      have hparent_blue_old : st.color parent = blue := by
        simpa [hne_t, hne_rem] using hparent_blue
      exact hinv.2.2.2.2.2.2.2.2.2.2.2.1 off parent child (hparent_block hne_rem) hparent_blue_old
    · simp [hsplit, hhead]
      intro off pred hpred_block hpred_blue hpred_next parent child hparent_block hparent_blue hne_t hne_rem
      have hparent_blue_old : st.color parent = blue := by
        simpa [hne_t, hne_rem] using hparent_blue
      exact hinv.2.2.2.2.2.2.2.2.2.2.2.1 off parent child (hparent_block hne_rem) hparent_blue_old
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hnosplit_head]
      intro off parent child hparent_block hparent_blue hne_t
      have hparent_blue_old : st.color parent = blue := by
        simpa [hne_t] using hparent_blue
      exact hinv.2.2.2.2.2.2.2.2.2.2.2.1 off parent child hparent_block hparent_blue_old
    · simp [hsplit, hhead]
      intro off pred hpred_block hpred_blue hpred_next parent child hparent_block hparent_blue hne_t
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  intro hphase hreq t ht ht_blue hsize_le
  by_cases hsplit : ↑reqSize < st.size t
  · by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hsplit_head]
      intro off parent child1 child2 hne_t₁ hne_rem₁ hfield1 hne_t₂ hne_rem₂ hfield2
      exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.1 off parent child1 child2 hfield1 hfield2
    · simp [hsplit, hhead]
      intro off pred hpred_block hpred_blue hpred_next parent child1 child2 hne_t₁ hne_rem₁ hfield1 hne_t₂ hne_rem₂ hfield2
      exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.1 off parent child1 child2 hfield1 hfield2
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hnosplit_head]
      intro off parent child1 child2 hne_t₁ hfield1 hne_t₂ hfield2
      exact hinv.2.2.2.2.2.2.2.2.2.2.2.2.1 off parent child1 child2 hfield1 hfield2
    · simp [hsplit, hhead]
      intro off pred hpred_block hpred_blue hpred_next parent child1 child2 hne_t₁ hfield1 hne_t₂ hfield2
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  intro hphase hreq t ht ht_blue hsize_le
  by_cases hsplit : ↑reqSize < st.size t
  · by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hsplit_head]
      intro off parent child hne_t hne_rem hfield
      have hbounds_old := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1 off parent child hfield
      simpa [hne_t, hne_rem] using hbounds_old
    · simp [hsplit, hhead]
      intro off pred hpred_block hpred_blue hpred_next parent child hne_t hne_rem hfield
      have hbounds_old := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1 off parent child hfield
      simpa [hne_t, hne_rem] using hbounds_old
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      simp [hhead, hnosplit_head]
      intro off parent child hne_t hfield
      have hbounds_old := hinv.2.2.2.2.2.2.2.2.2.2.2.2.2.1 off parent child hfield
      simpa [hne_t] using hbounds_old
    · simp [hsplit, hhead]
      intro off pred hpred_block hpred_blue hpred_next parent child hne_t hfield
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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  intro hphase hreq t ht ht_blue hsize_le
  rcases hinv with ⟨h_heap_start, h_block_heap, h_null_not_block, h_fits, h_no_overlap, h_next_by_size,
    h_valid_size, h_block_color, h_roots_alloc, h_fields_from, h_fields_to, h_free_no_fields,
    h_field_unique, h_field_bounds, h_free_next_wf, h_free_head_ok, h_free_next_after,
    h_free_next_unique, h_free_list_entry, h_swept_free_list_entry, h_tail_free, h_head_tail,
    h_tail_next_null, h_tail_before, h_alloc_next_unused, h_sweep_bounds, h_sweep_points,
    h_world_paused, h_white_before, h_roots_gray, h_black_edges, h_roots_black, h_no_black_white,
    h_white_child, h_mark_complete_colors, h_blue_no_child, h_blue_no_parent, h_roots_black_sweep,
    h_reach_black_sweep, h_roots_white_sweep, h_white_points_white⟩
  let rem := th.addrToPtr (th.ptrToAddr t + ↑reqSize)
  have ht_ne_rem : ¬t = rem := by
    intro h
    have hc := congrArg th.ptrToAddr h
    dsimp [rem] at hc
    rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hc
    omega
  by_cases hsplit : ↑reqSize < st.size t
  · by_cases hhead : t = st.free_head
    · have hsplit_head : ↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      simp [hhead, hsplit_head]
      intro ptr hptr_block hptr_blue hptr_next_ne
      by_cases hptr_t : t = ptr
      · subst ptr
        have hwhite_blue : white = blue := by
          simpa [hfree_t] using hptr_blue
        exact False.elim (Color_Enum.distinct.2.2.2.2.1 hwhite_blue.symm)
      · by_cases hptr_rem_head : th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize) = ptr
        · subst ptr
          intro hnew_next_ne
          have hnext_ne : ¬st.next t = th.null_ptr := by
            simpa [hfree_t] using hnew_next_ne
          have hnext_old := h_free_next_wf t ht ht_blue hnext_ne
          constructor
          · intro _
            simpa [rem, hfree_t, ht_ne_rem] using hnext_old.1
          · by_cases hnext_t : t = st.next t
            · have hafter := h_free_next_after t ht ht_blue hnext_ne
              have hafter' : th.ptrToAddr t + st.size t ≤ th.ptrToAddr t := by
                rw [← hnext_t] at hafter
                exact hafter.1
              have hpos := h_valid_size t ht
              omega
            · by_cases hnext_rem : rem = st.next t
              · simpa [rem, hfree_t, ht_ne_rem, hnext_t, hnext_rem]
              · simpa [rem, hfree_t, ht_ne_rem, hnext_t, hnext_rem] using hnext_old.2
        · have hptr_old : st.is_block ptr = true := hptr_block hptr_rem_head
          have hptr_blue_old : st.color ptr = blue := by
            have hfree_not_ptr : ¬st.free_head = ptr := by
              simpa [hhead] using hptr_t
            simpa [hfree_not_ptr, hptr_rem_head] using hptr_blue
          intro hnew_next_ne
          have hnext_ne : ¬st.next ptr = th.null_ptr := by
            simpa [hptr_t, hptr_rem_head] using hnew_next_ne
          have hnext_old := h_free_next_wf ptr hptr_old hptr_blue_old hnext_ne
          constructor
          · intro hnext_rem_head
            have hfree_not_ptr : ¬st.free_head = ptr := by
              simpa [hhead] using hptr_t
            simpa [hfree_not_ptr, hptr_rem_head] using hnext_old.1
          · have hnext_not_t : ¬t = st.next ptr := by
              intro hnext_t
              have hafter := h_free_next_after ptr hptr_old hptr_blue_old hnext_ne
              have ht_before : th.ptrToAddr ptr + st.size ptr ≤ th.ptrToAddr t := by
                simpa [hnext_t] using hafter.1
              by_cases hptr_before_t : th.ptrToAddr ptr < th.ptrToAddr t
              · have htptr := h_no_overlap ptr t hptr_old ht hptr_before_t
                omega
              · have hptr_addr_ne : th.ptrToAddr ptr ≠ th.ptrToAddr t := by
                  intro haddr
                  have hptr_eq : ptr = t := by
                    have hc := congrArg th.addrToPtr haddr
                    simpa [has.2.1 ptr, has.2.1 t] using hc
                  exact hptr_t hptr_eq.symm
                have ht_before_ptr : th.ptrToAddr t < th.ptrToAddr ptr := by
                  omega
                have htptr := h_no_overlap t ptr ht hptr_old ht_before_ptr
                omega
            by_cases hnext_rem_head : th.addrToPtr (th.ptrToAddr st.free_head + ↑reqSize) = st.next ptr
            · have hnext_rem : rem = st.next ptr := by
                dsimp [rem]
                simpa [hhead] using hnext_rem_head
                have hrem_block : st.is_block rem = true := by
                  rw [hnext_rem]
                  exact hnext_old.1
              have ht_lt_rem : th.ptrToAddr t < th.ptrToAddr rem := by
                dsimp [rem]
                rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
                omega
              have hoverlap := h_no_overlap t rem ht hrem_block ht_lt_rem
              dsimp [rem] at hoverlap
              rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hoverlap
              omega
              · have hfree_not_next : ¬st.free_head = st.next ptr := by
                  simpa [hhead] using hnext_not_t
                simpa [hfree_not_next, hnext_rem_head] using hnext_old.2
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next ptr hptr_block hptr_blue hptr_next_ne
      by_cases hptr_t : t = ptr
      · subst ptr
        have hwhite_blue : white = blue := by
          simpa using hptr_blue
        exact False.elim (Color_Enum.distinct.2.2.2.2.1 hwhite_blue.symm)
      · by_cases hptr_rem : rem = ptr
        · subst ptr
          intro hnew_next_ne
          have hnext_ne : ¬st.next t = th.null_ptr := by
            simpa [rem] using hnew_next_ne
          have hnext_old := h_free_next_wf t ht ht_blue hnext_ne
          constructor
          · intro _
            simpa [rem, ht_ne_rem] using hnext_old.1
          · by_cases hnext_t : t = st.next t
            · have hafter := h_free_next_after t ht ht_blue hnext_ne
                have hafter' : th.ptrToAddr t + st.size t ≤ th.ptrToAddr t := by
                  rw [← hnext_t] at hafter
                  exact hafter.1
              have hpos := h_valid_size t ht
              omega
            · by_cases hnext_rem : rem = st.next t
              · simpa [rem, ht_ne_rem, hnext_t, hnext_rem]
              · simpa [rem, ht_ne_rem, hnext_t, hnext_rem] using hnext_old.2
          · by_cases hpred : st.is_block ptr = true ∧ st.color ptr = blue ∧ st.next ptr = t
            · intro hnew_next_ne
              constructor
            · intro hnext_null
              have ht_null : t = th.null_ptr := by
                simpa [hptr_t, hptr_rem, hpred] using hnext_null
              have hnull_block : st.is_block th.null_ptr = true := by
                simpa [ht_null] using ht
              simpa [h_null_not_block] using hnull_block
            · simp [rem, ht_ne_rem, hptr_t, hptr_rem, hpred]
            · have hptr_old : st.is_block ptr = true := hptr_block hptr_rem
              have hptr_blue_old : st.color ptr = blue := by
                simpa [hptr_t, hptr_rem] using hptr_blue
              intro hnew_next_ne
              have hnext_ne : ¬st.next ptr = th.null_ptr := by
                simpa [hptr_t, hptr_rem, hpred] using hnew_next_ne
              have hnext_old := h_free_next_wf ptr hptr_old hptr_blue_old hnext_ne
              constructor
              · intro _
                simpa [hptr_t, hptr_rem, hpred] using hnext_old.1
              · have hnext_not_t : ¬t = st.next ptr := by
                  intro hnext_t
                  exact hpred ⟨hptr_old, hptr_blue_old, hnext_t.symm⟩
                by_cases hnext_rem : rem = st.next ptr
                · have hrem_block : st.is_block rem = true := by
                    rw [hnext_rem]
                    exact hnext_old.1
                  have ht_lt_rem : th.ptrToAddr t < th.ptrToAddr rem := by
                    dsimp [rem]
                    rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)]
                    omega
                  have hoverlap := h_no_overlap t rem ht hrem_block ht_lt_rem
                  dsimp [rem] at hoverlap
                  rw [has.2.2.2.1 (th.ptrToAddr t + ↑reqSize)] at hoverlap
                  omega
                · simpa [rem, hptr_t, hptr_rem, hpred, hnext_not_t, hnext_rem] using hnext_old.2
  · by_cases hhead : t = st.free_head
    · have hnosplit_head : ¬↑reqSize < st.size st.free_head := by
        simpa [hhead] using hsplit
      have hfree_t : st.free_head = t := hhead.symm
      simp [hhead, hnosplit_head]
      intro ptr hptr_block hptr_blue hptr_next_ne
      by_cases hptr_t : t = ptr
      · subst ptr
        have hwhite_blue : white = blue := by
          simpa [hfree_t] using hptr_blue
        exact False.elim (Color_Enum.distinct.2.2.2.2.1 hwhite_blue.symm)
      · have hptr_old : st.is_block ptr = true := hptr_block
        have hptr_blue_old : st.color ptr = blue := by
          have hfree_not_ptr : ¬st.free_head = ptr := by
            simpa [hhead] using hptr_t
          simpa [hfree_not_ptr] using hptr_blue
          intro hnew_next_ne
          have hnext_ne : ¬st.next ptr = th.null_ptr := by
            simpa [hptr_t] using hnew_next_ne
        have hnext_old := h_free_next_wf ptr hptr_old hptr_blue_old hnext_ne
        constructor
        · exact hnext_old.1
        · have hnext_not_t : ¬t = st.next ptr := by
            intro hnext_t
            have ht_next : st.next ptr = t := hnext_t.symm
            have hafter := h_free_next_after ptr hptr_old hptr_blue_old hnext_ne
            have hptr_before_t : th.ptrToAddr ptr + st.size ptr ≤ th.ptrToAddr t := by
              simpa [ht_next] using hafter.1
            by_cases hlt : th.ptrToAddr ptr < th.ptrToAddr t
            · have hoverlap := h_no_overlap ptr t hptr_old ht hlt
              omega
            · have haddr_ne : th.ptrToAddr ptr ≠ th.ptrToAddr t := by
                intro haddr
                have hc := congrArg th.addrToPtr haddr
                have hptr_eq_t : ptr = t := by
                  simpa [has.2.1 ptr, has.2.1 t] using hc
                exact hptr_t hptr_eq_t.symm
              have ht_lt_ptr : th.ptrToAddr t < th.ptrToAddr ptr := by omega
              have hoverlap := h_no_overlap t ptr ht hptr_old ht_lt_ptr
              omega
          simpa [hptr_t, hnext_not_t] using hnext_old.2
    · simp [hsplit, hhead]
      intro pred hpred_block hpred_blue hpred_next ptr hptr_block hptr_blue hptr_next_ne
      by_cases hptr_t : t = ptr
      · subst ptr
        have hwhite_blue : white = blue := by
          simpa using hptr_blue
        exact False.elim (Color_Enum.distinct.2.2.2.2.1 hwhite_blue.symm)
      · by_cases hpred : st.is_block ptr = true ∧ st.color ptr = blue ∧ st.next ptr = t
        · intro hnew_next_ne
          have hnext_ne : ¬st.next t = th.null_ptr := by
            simpa [hptr_t, hpred] using hnew_next_ne
          have hnext_old := h_free_next_wf t ht ht_blue hnext_ne
          constructor
          · simpa [hptr_t, hpred] using hnext_old.1
          · have hnext_not_t : ¬t = st.next t := by
              intro hnext_t
              have hafter := h_free_next_after t ht ht_blue hnext_ne
                have hafter' : th.ptrToAddr t + st.size t ≤ th.ptrToAddr t := by
                  rw [← hnext_t] at hafter
                  exact hafter.1
              have hpos := h_valid_size t ht
              omega
            simpa [hptr_t, hpred, hnext_not_t] using hnext_old.2
        · have hptr_blue_old : st.color ptr = blue := by
            simpa [hptr_t] using hptr_blue
          intro hnew_next_ne
          have hnext_ne : ¬st.next ptr = th.null_ptr := by
            simpa [hptr_t, hpred] using hnew_next_ne
          have hnext_old := h_free_next_wf ptr hptr_block hptr_blue_old hnext_ne
          constructor
          · simpa [hptr_t, hpred] using hnext_old.1
          · have hnext_not_t : ¬t = st.next ptr := by
              intro hnext_t
              exact hpred ⟨hptr_block, hptr_blue_old, hnext_t.symm⟩
            simpa [hptr_t, hpred, hnext_not_t] using hnext_old.2

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  sorry

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  sorry

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  sorry

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  sorry

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  sorry

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  sorry

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
    [σ_sub : IsSubStateOf (@State χ) σ] [ρ_sub : IsSubReaderOf (@Theory Mutator Collector Ptr HeapSize Color Phase) ρ] :
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  sorry

theorem Allocate_color_implies_block (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
        (@Assumptions ρ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum ρ_sub)
        (@Invariants ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub)
        (@color_implies_block ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq
          Collector_inhabited Ptr Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited
          Color_Enum Phase Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub) :=
  by
  veil_human
  sorry

theorem Allocate_gray_only_in_mark (ρ : Type) (σ : Type) (Mutator : Type) [Mutator_dec_eq : DecidableEq.{1} Mutator]
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
    ∀ (_m : Mutator) (reqSize : Fin (Nat.succ HeapSize)),
      Veil.VeilM.meetsSpecificationIfSuccessfulAssuming
        (@Allocate.ext ρ σ Mutator Mutator_dec_eq Mutator_inhabited Collector Collector_dec_eq Collector_inhabited Ptr
          Ptr_dec_eq Ptr_inhabited HeapSize heapSizeNonzero Color Color_dec_eq Color_inhabited Color_Enum Phase
          Phase_dec_eq Phase_inhabited Phase_Enum χ χ_rep χ_rep_lawful σ_sub ρ_sub _m reqSize)
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
  sorry
