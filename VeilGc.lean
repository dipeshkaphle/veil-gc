import Veil

/-!
An initial Veil skeleton for the stop-the-world mark-and-sweep collector
described in `Project/verifiedgc_feb_25.pdf`.

This file intentionally captures the collector kernel first:
- abstract objects and roots
- tricolour state plus free objects
- mark stack
- sweep bookkeeping
- stop-the-world collector phases

The abstract graph-reachability specification from the paper is the next layer
to add on top of this state machine. It is not encoded yet in this first pass.
-/
set_option veil.solver "grindAndSMT"

veil module VerifiedGc

type Mutator

type Collector

type Ptr

-- the heap is a contiguous region of memory from heap_start to heap_end

param HeapSize: Nat
instantiate heapSizeNonzero : NeZero HeapSize

enum Color = { uncolored, blue, white, gray, black }
enum Phase = { idle,
               gc_requested,
               darken_roots, darken_roots_complete,
               mark, mark_complete,
               sweep, reset_colors, sweep_complete }

immutable individual heap_start : Ptr
immutable individual null_ptr : Ptr
immutable function ptrToAddr : Ptr → Nat
immutable function addrToPtr : Nat → Ptr


individual phase : Phase

-- `free_head` is the concrete entry point of the free list used by allocation.
-- During sweep, `sweep_addr` is the address cursor for the next block to
-- inspect, and `free_tail` remembers the last free block already rebuilt below
-- `sweep_addr`, so the next swept free block can be appended after it.
--
--   heap_start                                    heap_start + HeapSize
--      |                                                     |
--      v                                                     v
--   [ already swept / rebuilt free-list prefix ][ not swept yet ]
--                                      ^
--                                      sweep_addr
--
-- If the rebuilt prefix contains free blocks, `free_head` is the first one and
-- `free_tail` is the last one:
--
--   free_head --> ... --> free_tail --> null_ptr
--
-- So adding the next swept free block only needs to update `next free_tail`.
individual sweep_addr : Nat
individual free_head : Ptr
individual free_tail : Ptr

-- indicates that a mutator is paused
relation world_paused : Mutator → Bool

/-

We maintain a free-list here in a way.

- If color of an address is blue, then it is free.
- The size of each free block/address has to be more than 0, since the free part is to be used to point to the next free block, and the size of the free block is used to calculate the next free block.
- If it's any other color, then it's allocated.

- We define a block to be some address in heap, something that has a color, and a size
- A block may be allocated or free(blue color)
- is_block is a way to say that this address is not some random address in the middle of the heap.
-/
function next (a: Ptr) : Ptr

-- the global roots
relation roots : Ptr → Bool

-- represents the color of the currently allocated object
function color (obj: Ptr) : Color

-- size of an object
function size (obj: Ptr) : Nat

relation is_block : Ptr -> Bool

/-
- We have a heap
Heap is a free list right..

So we have a starting addr , and the size of that thing..

heap a <sz>

We can then do an allocation of a certain size, which should split this heap.

heap a <sz> -> alloc a sz' -> heap (a + sz') <sz - sz'>, obj a sz'

so, now at addr a , we have some object, with a certain color..

-/

/-
Given,
```
type foo = {
  x: bar
}
`(parent: foo).x = (child: bar)`

x is the first field, so we say its at offset 0 and hence this is represented as `field parent 0 child`.
-/

relation field (parent: Ptr) (offset: Fin (Nat.succ HeapSize)) (child: Ptr) : Bool


#gen_state

after_init {
  phase := idle
  color O := uncolored
  roots O := false
  sweep_addr := ptrToAddr heap_start
  free_head := heap_start
  free_tail := null_ptr
  next O := null_ptr
  size O := 0
  is_block O := false
  field P O C := false
  size heap_start := HeapSize
  -- this is outside the heap range, so we automaticaly don't care about this since it's invalid
  next heap_start := null_ptr
  color heap_start := blue
  is_block heap_start := true
  world_paused M := false
}

assumption [heap_size_gt_zero] HeapSize > 0
assumption [ptr_roundtrip] ∀ ptr, addrToPtr (ptrToAddr ptr) = ptr
assumption [addr_roundtrip_on_heap] ∀ raw,
  ptrToAddr heap_start ≤ raw ∧ raw < ptrToAddr heap_start + HeapSize →
    ptrToAddr (addrToPtr raw) = raw
assumption [addr_roundtrip] ∀ raw,
  ptrToAddr (addrToPtr raw) = raw
assumption [null_ptr_outside_heap]
  ¬ (ptrToAddr heap_start ≤ ptrToAddr null_ptr ∧
    ptrToAddr null_ptr < ptrToAddr heap_start + HeapSize)


procedure setNext (ptr : Ptr) (nxt : Ptr) {
  next ptr := nxt
}

procedure setNextOfPred (target : Ptr) (nxt : Ptr) {
  -- Redirect any free predecessor whose next pointer currently targets `target`.
  next P := if is_block P ∧ color P = blue ∧ next P = target then nxt else next P
}

action Allocate (_m: Mutator) (reqSize : Fin (Nat.succ HeapSize)) {
  require phase = idle
  require reqSize.val > 0

  let ptr : Ptr ← pick
  require is_block ptr
  require color ptr = blue
  require ptr = free_head ∨
    ∃ pred, is_block pred ∧ color pred = blue ∧ next pred = ptr

  let oldSize := size ptr
  let oldNext := next ptr
  require oldSize >= reqSize.val

  -- Split a larger free block: predecessors now point to the remainder.
  if oldSize > reqSize.val then
    let remainder := addrToPtr (ptrToAddr ptr + reqSize.val)
    setNextOfPred ptr remainder
    if ptr = free_head then
      free_head := remainder
    is_block remainder := true
    color remainder := blue
    size remainder := oldSize - reqSize.val
    setNext remainder oldNext
    field remainder O C := false
  -- Exact fit: splice this block out of the free list entirely.
  else
    setNextOfPred ptr oldNext
    if ptr = free_head then
      free_head := oldNext

  color ptr := white
  size ptr := reqSize.val
  setNext ptr null_ptr
  field ptr O C := false
}


action Update (_m: Mutator) (parent: Ptr) (offset: Fin (Nat.succ HeapSize)) (child: Ptr) {
  require phase = idle
  require is_block parent ∧ color parent ≠ blue
  require is_block child ∧ color child ≠ blue
  require offset.val < size parent

  field parent offset C := false
  field parent offset child := true
}

action AddRoot (_m : Mutator) (ptr : Ptr) {
  require phase = idle
  require is_block ptr ∧ color ptr ≠ blue
  require ¬ roots ptr

  roots ptr := true
}

action DropRoot (_m : Mutator) (ptr : Ptr) {
  require phase = idle
  require roots ptr

  roots ptr := false
}

-- some mutator may not have realized that there's not enough space.
-- In that case, they might say I want some memory, so clean some garbage..
action InitiateGC (_m : Mutator) {
  require phase = idle

  phase := gc_requested
}

-- if a gc has been requested, we need all the mutators to pause their world
action Pause (m: Mutator) {
  require phase = gc_requested

  world_paused m := true
}


-- once every mutator has paused, we start the GC cycle
action BeginGC(_c: Collector){
  require phase = gc_requested
  require ∀ m, world_paused m = true

  phase := darken_roots
}


action DarkenRoot (_c: Collector){
  require phase = darken_roots

  -- pick an arbitrary root, color it gray (it's kinda like putting it on the marking stack)
  let root_ptr : Ptr <- pick
  require is_block root_ptr -- is a valid block
  require roots root_ptr
  require color root_ptr != gray -- not already colored

  color root_ptr := gray
}

action CompleteDarkenRoot (_c: Collector){
  require phase = darken_roots
  require ∀ ptr, roots ptr → color ptr = gray

  -- since the initial stack has been set up
  phase := darken_roots_complete
}

action BeginMarking(_c: Collector){
  require phase = darken_roots_complete

  phase := mark
}

action MarkStep (_c : Collector) {
  require phase = mark

  -- pick an arbitrary ptr, gray in color..
  -- mark its children gray
  -- make its color black
  let curr_ptr : Ptr <- pick
  require is_block curr_ptr
  require color curr_ptr = gray -- must have been marked gray (either by DarkenRoot, or by a MarkStep call)

  -- The child-side block/color checks make sure we only gray allocated children.
  -- then we just make sure that it's not black either,
  -- if it's black it means all its children have been visited
  -- so we don't want to do anything to it
  color P := if (∃ offset, field curr_ptr offset P) ∧
      is_block P ∧ color P ≠ blue ∧ color P ≠ black
    then gray else color P

  -- mark the current thing as black since we already visited all its children and made them gray
  -- its children will be scanned later
  color curr_ptr := black
}


action FinishMarking (_c : Collector) {
  require phase = mark
  require ∀ ptr, is_block ptr -> color ptr ≠ gray -- no grays left..

  phase := mark_complete
}

-- I think we need to capture all the things that are white here..
-- Extra book keeping just to maybe assert things later on ?
action BeginSweep (_c: Collector) {
  require phase = mark_complete

  sweep_addr := ptrToAddr heap_start
  free_head := null_ptr
  free_tail := null_ptr
  phase := sweep
}


-- TODO: coalescing
action SweepStep (_c : Collector) {
  require phase = sweep

  let curr : Ptr := addrToPtr sweep_addr
  require ptrToAddr heap_start ≤ sweep_addr
  require sweep_addr < ptrToAddr heap_start + HeapSize
  require is_block curr
  require color curr = black ∨ color curr = white ∨ color curr = blue

  let oldSize := size curr

  if color curr = black then
    -- Live blocks stay allocated. Their `next` is already null by
    -- `allocated_block_next_unused`, so sweep does not touch it.
    sweep_addr := sweep_addr + oldSize
  else
    -- Dead allocated blocks become free, and old free blocks are reinserted
    -- into the rebuilt list. The scan is by increasing address, so appending
    -- preserves address order.
    field curr O C := false
    color curr := blue
    if free_tail = null_ptr then
      free_head := curr
    else
      setNext free_tail curr
    free_tail := curr
    setNext curr null_ptr
    sweep_addr := sweep_addr + oldSize
}

action CompleteSweep (_c : Collector) {
  require phase = sweep
  require sweep_addr = ptrToAddr heap_start + HeapSize
  -- everything is either blue(free), or black(white ones were marked unreachable and recolored to blue)
  -- gray cannot happen since it can only exist during marking phase
  require ∀ ptr, is_block ptr -> color ptr != white

  phase := reset_colors

}

action ResetReachable (_c: Collector){
  require phase = reset_colors

  -- everything reachable (i.e black) is made white to complete the full GC cycle
  color P := if color P = black then white else color P

  phase := sweep_complete
}


action CompleteGC (_c: Collector) {
  require phase = sweep_complete

  -- unpause everyone's world
  world_paused M := false
  free_tail := null_ptr
  phase := idle
}


invariant [heap_start_is_block]
 is_block heap_start

invariant [block_always_lies_in_heap] ∀ ptr, is_block ptr →
  ptrToAddr heap_start ≤ ptrToAddr ptr ∧ ptrToAddr ptr < ptrToAddr heap_start + HeapSize

invariant [null_ptr_not_block]
  ¬ is_block null_ptr

invariant [block_fits_in_heap]
  ∀ ptr, is_block ptr →
    ptrToAddr ptr + size ptr ≤ ptrToAddr heap_start + HeapSize

invariant [blocks_do_not_overlap]
  ∀ p q,
    is_block p ∧ is_block q ∧ ptrToAddr p < ptrToAddr q →
      ptrToAddr p + size p ≤ ptrToAddr q

invariant [block_next_by_size_is_block]
  ∀ p, is_block p →
    let nextAddr := ptrToAddr p + size p
    nextAddr = ptrToAddr heap_start + HeapSize ∨
      is_block (addrToPtr nextAddr)


invariant [block_has_valid_size]
   ∀ ptr, is_block ptr → size ptr > 0
invariant [block_has_color]
  ∀ ptr, is_block ptr → color ptr ≠ uncolored
invariant [roots_are_allocated]
  ∀ ptr, roots ptr → is_block ptr ∧ color ptr ≠ blue

-- field invariants
invariant [fields_from_allocated]
  ∀ parent off child, field parent off child →
    is_block parent ∧ color parent ≠ blue
invariant [fields_to_allocated]
  ∀ parent off child, phase ≠ sweep ∧ field parent off child →
    is_block child ∧ color child ≠ blue
invariant [free_blocks_have_no_fields]
  ∀ parent off child, is_block parent ∧ color parent = blue → ¬ field parent off child

invariant [field_unique]
  ∀ parent off child1 child2,
    field parent off child1 ∧ field parent off child2 → child1 = child2
invariant [field_is_in_bounds]
  ∀ parent off child, field parent off child → off.val < size parent

-- Free blocks have a next pointer means the next pointer is also
-- free
invariant [free_block_next_wellformed]
  ∀ ptr, is_block ptr ∧ color ptr = blue ∧ next ptr ≠ null_ptr →
    is_block (next ptr) ∧ color (next ptr) = blue

invariant [free_head_is_free_or_null]
  free_head = null_ptr ∨ is_block free_head ∧ color free_head = blue

-- The free list is address ordered. This rules out self-loops, backward links,
-- and cycles in the `next` chain.
invariant [free_next_after_block]
  ∀ ptr, is_block ptr ∧ color ptr = blue ∧ next ptr ≠ null_ptr →
    ptrToAddr ptr + size ptr ≤ ptrToAddr (next ptr)

invariant [free_next_unique_predecessor]
  ∀ pred1 pred2 target,
    is_block pred1 ∧ color pred1 = blue ∧
    is_block pred2 ∧ color pred2 = blue ∧
    next pred1 = target ∧ next pred2 = target ∧
    target ≠ null_ptr →
      pred1 = pred2

-- Outside sweep, every free block is either the list head or has a free
-- predecessor. Together with address-ordered links, this rules out disconnected
-- free islands without needing a recursive reachability relation here.
invariant [free_blocks_have_list_entry]
  phase ≠ sweep →
    ∀ ptr, is_block ptr ∧ color ptr = blue →
      ptr = free_head ∨
        ∃ pred, is_block pred ∧ color pred = blue ∧ next pred = ptr

-- During sweep the list is being rebuilt, so only the swept prefix is expected
-- to have an entry in the rebuilt list.
invariant [swept_free_blocks_have_list_entry]
  phase = sweep →
    ∀ ptr, is_block ptr ∧ color ptr = blue ∧ ptrToAddr ptr + size ptr ≤ sweep_addr →
      ptr = free_head ∨
        ∃ pred, is_block pred ∧ color pred = blue ∧ next pred = ptr

invariant [free_tail_is_free_during_sweep]
  phase = sweep ∧ free_tail ≠ null_ptr →
    is_block free_tail ∧ color free_tail = blue

invariant [free_head_tail_empty_together_during_sweep]
  phase = sweep →
    (free_head = null_ptr ↔ free_tail = null_ptr)

invariant [free_tail_next_is_null_during_sweep]
  phase = sweep ∧ free_tail ≠ null_ptr →
    next free_tail = null_ptr

invariant [free_tail_before_sweep_addr]
  phase = sweep ∧ free_tail ≠ null_ptr →
    ptrToAddr free_tail + size free_tail ≤ sweep_addr

-- allocated block has no next ptr
invariant [allocated_block_next_unused]
  ∀ ptr, is_block ptr ∧ color ptr ≠ blue →
    next ptr = null_ptr

invariant [sweep_addr_in_bounds]
  phase = sweep →
    ptrToAddr heap_start ≤ sweep_addr ∧
      sweep_addr ≤ ptrToAddr heap_start + HeapSize

invariant [sweep_addr_points_to_block]
  phase = sweep ∧ sweep_addr < ptrToAddr heap_start + HeapSize →
    is_block (addrToPtr sweep_addr)

-- stop-the-world when doing GC(mark and sweep)
invariant [world_paused_during_gc] ∀ m , (phase != idle ∧ phase != gc_requested ) ->  world_paused m


-- everything block is either blue or white during gc_requested phase as well
invariant [allocated_white_before_coloring]
 ∀ p, (phase = idle ∨ phase = gc_requested) ∧
    is_block p ∧ color p ≠ blue →
      color p = white

-- when we are at mark phase, every root must've been colored gray(meaning its to be scanned during marking)
invariant [all_roots_marked_gray_before_mark_phase] ∀ r, roots r ∧ phase = darken_roots_complete -> color r = gray


-- if some ptr is marked black during mark, all of its field
-- must be either gray (will be scanned later) or black (already scanned)
invariant [only_black_to_gray_or_black_during_mark]
  ∀ p off c,
    phase = mark ∧ color p = black ∧ field p off c →
      color c = black ∨ color c = gray

invariant [all_roots_marked_black_after_mark_phase] ∀ r, roots r ∧ phase = mark_complete -> color r = black

-- post marking (in mark_complete) phase, we have only black -> black
invariant [no_black_to_white_after_mark]
  ∀ p off c,
    phase = mark_complete ∧ color p = black ∧ field p off c →
      color c = black

-- if a ptr has white color, then all its parents must be colored white as well
-- Doesn't make sense to say white -> white edge, since the child might be
-- reachable in other ways and may have been marked black.
-- However, if a child is white, it must mean every parent of that child is also white.
invariant [white_child_implies_all_white_parents]
  ∀ p off c,
    phase = mark_complete ∧ color c = white ∧ field p off c →
      color p = white

invariant [only_black_white_and_blue_in_mark_complete]
  ∀ p,
    phase = mark_complete ∧ is_block p →
      color p = blue ∨ color p = white ∨ color p = black

invariant [blue_never_child_outside_sweep]
  ∀ p,
    phase ≠ sweep ∧ is_block p ∧ color p = blue  →
      ¬ (∃ parent off, is_block parent ∧ field parent off p)

invariant [blue_never_parent]
  ∀ p,
    is_block p ∧ color p = blue  →
      ¬ (∃ child off, is_block child ∧ field p off child)

invariant [roots_black_during_after_unreachables_sweeping]
    ∀ r, roots r ∧ phase = sweep -> color r = black

invariant [reachables_still_black_after_unreachables_sweeping]
  ∀ p off c,
    phase = sweep ∧ color p = black ∧ field p off c →
      color c = black


invariant [all_roots_white_after_sweep] ∀ r , phase = sweep_complete ∧ roots r -> color r = white

-- if a field is white, all it's children are also white
invariant [all_white_points_to_white_after_sweep] ∀ ptr child ,
          phase = sweep_complete ∧
            is_block ptr ∧ is_block child ∧ (∃ off, field ptr off child) ∧
              color ptr = white -> color child = white

#gen_spec


 --#model_check
   --{ Mutator := Fin 1, Collector := Fin 1, Ptr := Fin 10, HeapSize := 6 }
   --{ heap_start := (2 : Fin 10),
     --null_ptr := (0 : Fin 10),
     --ptrToAddr := fun p => p.val,
     --addrToPtr := fun n => Fin.ofNat 10 n }

/- #check RelationalTransitionSystem -/

@[veil]
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

@[veil]
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

@[veil]
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

@[veil]
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

@[veil]
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

@[veil]
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

@[veil]
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


@[veil]
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
  sorry

@[veil]
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

@[veil]
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

@[veil]
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
    have hparent_blue_old : st.color parent = blue := by
      simpa [hne_t, hne_rem] using hparent_blue
    exact hinv.2.2.2.2.2.2.2.2.2.2.2.1 off parent child (hparent_block hne_rem) hparent_blue_old
  · intro off parent child hparent_block hparent_blue hne_t
    have hparent_blue_old : st.color parent = blue := by
      simpa [hne_t] using hparent_blue
    exact hinv.2.2.2.2.2.2.2.2.2.2.2.1 off parent child hparent_block hparent_blue_old

@[veil]
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

@[veil]
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

@[veil]
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
  sorry

@[veil]
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

@[veil]
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
  sorry

@[veil]
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
  sorry

@[veil]
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
  sorry

@[veil]
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

@[veil]
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

@[veil]
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

@[veil]
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
      exact h_blue_no_parent off t ht hblue child (hchild_block hne_rem)
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
        exact h_blue_no_parent off p hp_block_old hp_blue_old child (hchild_block hne_rem)
  · intro off p hp_block hp_blue child hchild_block hne_t
    by_cases hpt : t = p
    · subst p
      exact h_blue_no_parent off t ht hblue child hchild_block
    · have hp_blue_old : st.color p = blue := by
        simpa [hpt] using hp_blue
      exact h_blue_no_parent off p hp_block hp_blue_old child hchild_block

-- #check_action Allocate

end VerifiedGc
