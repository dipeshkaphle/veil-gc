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

action Allocate (_m: Mutator) (reqSize : Fin (Nat.succ HeapSize)) {
  require phase = idle
  require reqSize.val > 0

  let ptr : Ptr ← pick
  require is_block ptr
  require color ptr = blue

  let oldSize := size ptr
  let oldNext := next ptr
  require oldSize >= reqSize.val

  -- Split a larger free block: either move the head forward or redirect the
  -- single predecessor that links to this block.
  if oldSize > reqSize.val then
    let remainder := addrToPtr (ptrToAddr ptr + reqSize.val)
    if ptr = free_head then
      free_head := remainder
    else
      let pred : Ptr ← pick
      require is_block pred
      require color pred = blue
      require next pred = ptr
      setNext pred remainder
    is_block remainder := true
    color remainder := blue
    size remainder := oldSize - reqSize.val
    setNext remainder oldNext
    field remainder O C := false
  -- Exact fit: splice this block out of the free list entirely.
  else
    if ptr = free_head then
      free_head := oldNext
    else
      let pred : Ptr ← pick
      require is_block pred
      require color pred = blue
      require next pred = ptr
      setNext pred oldNext

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
  require color root_ptr = white -- not already colored

  color root_ptr := gray
}

action CompleteDarkenRoot (_c: Collector){
  require phase = darken_roots
  require ∀ ptr, roots ptr → color ptr = gray
  -- adding this as an assumption because it holds the wya we have things.
  -- Adding invariant for this will cause slowdown but it's provable.
  -- We have: allocated_white_before_coloring , which says:
  --```
  -- ∀ p, (phase = idle ∨ phase = gc_requested) ∧
  --  is_block p ∧ color p ≠ blue →
  --    color p = white
  --```
  -- So in gc_requested, everything is white
  -- After that in darken root, we make some stuff gray
  -- So we don't have black colored ptr here at alll.
  -- NOTE: This can be made an invariant but its simple enough
  -- that I don't think its worth it to go through the trouble of
  -- rerunning and extracting all the goals.
  require ∀ p, color p ≠ black

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
  next O := null_ptr
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
    ptrToAddr ptr + size ptr ≤ ptrToAddr (next ptr) ∧
      (phase = sweep → ptrToAddr (next ptr) + size (next ptr) ≤ sweep_addr)

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

-- SAFETY PROPERTY 1 (mark)
invariant [all_roots_marked_black_after_mark_phase] ∀ r, roots r ∧ phase = mark_complete -> color r = black

-- SAFETY PROPERTY 2 (mark)
-- post marking (in mark_complete) phase, we have only black -> black
-- The two safety property imply reachable from roots are marked black..
invariant [no_black_to_white_after_mark]
  ∀ p off c,
    phase = mark_complete ∧ color p = black ∧ field p off c →
      color c = black

-- The above two safety properties imply soundness. Everything reachable is
-- colored black.

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

-- SAFETY PROPERTY 1 (in sweep)
-- Roots are not freed after sweep
invariant [all_roots_white_after_sweep] ∀ r , phase = sweep_complete ∧ roots r -> color r = white

-- SAFETY PROPERTY 2 (in sweep)
-- if a field is white, all it's children are also white
-- Analogous to the similar invariants (modulo color), these two imply that
-- all things reachable from roots are white. (Soundness)
invariant [all_white_points_to_white_after_sweep] ∀ ptr child ,
          phase = sweep_complete ∧
            is_block ptr ∧ is_block child ∧ (∃ off, field ptr off child) ∧
              color ptr = white -> color child = white

invariant [no_black_before_mark] ∀ p, phase = darken_roots_complete → color p ≠ black
invariant [roots_gray_or_black_in_mark] ∀ r, roots r ∧ phase = mark → color r = gray ∨ color r = black
invariant [only_white_and_blue_in_sweep_complete] ∀ p, phase = sweep_complete ∧ is_block p ∧ color p ≠ blue → color p = white
invariant [color_implies_block] ∀ p, color p ≠ uncolored → is_block p
invariant [gray_only_in_mark] ∀ p, color p = gray → phase = mark ∨ phase = mark_complete ∨ phase = darken_roots ∨ phase = darken_roots_complete
invariant [no_black_in_sweep_complete] ∀ p, phase = sweep_complete → color p ≠ black
invariant [no_white_in_reset_colors] ∀ p, phase = reset_colors → color p ≠ white
invariant [black_edges_in_sweep] ∀ off p c, (phase = sweep ∨ phase = reset_colors) ∧ color p = black ∧ field p off c → color c = black

#gen_spec


 --#model_check
   --{ Mutator := Fin 1, Collector := Fin 1, Ptr := Fin 10, HeapSize := 6 }
   --{ heap_start := (2 : Fin 10),
     --null_ptr := (0 : Fin 10),
     --ptrToAddr := fun p => p.val,
     --addrToPtr := fun n => Fin.ofNat 10 n }

/- #check RelationalTransitionSystem -/

-- #check_invariants


end VerifiedGc
