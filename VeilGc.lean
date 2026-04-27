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


set_option veil.solver "grind"
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
               sweep, sweep_unreachable_done, reset_colors, sweep_complete }

immutable individual heap_start : Ptr
immutable individual null_ptr : Ptr
immutable function ptrToAddr : Ptr → Nat
immutable function addrToPtr : Nat → Ptr


individual phase : Phase

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

We can then do an allocation of a certain size, which should split this heap ideally somehow.
Not exactly split per se I guess..

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

ghost relation is_free (ptr : Ptr) := is_block ptr ∧ color ptr = blue
ghost relation is_allocated (ptr : Ptr) := is_block ptr ∧ color ptr ≠ blue ∧ color ptr ≠ uncolored

-- TODO: is this problematic since I use existential?
ghost relation field_of (parent: Ptr) (child: Ptr) := is_block parent ∧ is_block child ∧ (∃ offset, field parent offset child)

-- I cannot directly encode reachability that easily I guess.
-- One idea to prove that everything reachable from root is marked black
-- is by maybe taking some invariants as assumptions and then proving the final
-- reachability goal somehow, I am not sure if Veil has a mechanism for that though..
/- ghost relation reachable (parent: Ptr) (child: Ptr) :=
 -       (field_of parent child) ∨
 -       (¬ (field_of parent child) -> ∃ c', field_of parent c' ∧ reachable c' child)  -/


-- Reachable
-- R a a
-- R a b if a-> b is a filed


after_init {
  phase := idle
  color O := uncolored
  roots O := false
  next O := null_ptr
  size O := 0
  is_block O := false
  field P O C := false
  size heap_start := HeapSize
  -- this is outside the heap range, so we automaticaly don't care about this since it's invalid
  next heap_start := null_ptr
  color heap_start := blue
  is_block heap_start := true
}

assumption [heap_size_gt_zero] HeapSize > 0
assumption [ptr_roundtrip] ∀ ptr, addrToPtr (ptrToAddr ptr) = ptr
assumption [addr_roundtrip_on_heap] ∀ raw,
  ptrToAddr heap_start ≤ raw ∧ raw < ptrToAddr heap_start + HeapSize →
    ptrToAddr (addrToPtr raw) = raw
assumption [null_ptr_outside_heap]
  ¬ (ptrToAddr heap_start ≤ ptrToAddr null_ptr ∧
    ptrToAddr null_ptr < ptrToAddr heap_start + HeapSize)


procedure setNext (ptr : Ptr) (nxt : Ptr) {
  next ptr := nxt
}

procedure setNextOfPred (target : Ptr) (nxt : Ptr) {
  -- Redirect any free predecessor whose next pointer currently targets `target`.
  next P := if is_free P ∧ next P = target then nxt else next P
}

action allocate (_m: Mutator) (reqSize : Fin (Nat.succ HeapSize)) {
  require phase = idle
  require reqSize.val > 0

  let ptr : Ptr ← pick
  require is_block ptr
  require color ptr = blue

  let oldSize := size ptr
  let oldNext := next ptr
  require oldSize >= reqSize.val

  -- Split a larger free block: predecessors now point to the remainder.
  if oldSize > reqSize.val then
    let remainder := addrToPtr (ptrToAddr ptr + reqSize.val)
    setNextOfPred ptr remainder
    is_block remainder := true
    color remainder := blue
    size remainder := oldSize - reqSize.val
    setNext remainder oldNext
    field remainder O C := false
  -- Exact fit: splice this block out of the free list entirely.
  else
    setNextOfPred ptr oldNext

  color ptr := white
  size ptr := reqSize.val
  setNext ptr null_ptr
  field ptr O C := false
}


action Update (_m: Mutator) (parent: Ptr) (offset: Fin (Nat.succ HeapSize)) (child: Ptr) {
  require phase = idle
  require is_allocated parent
  require is_allocated child
  require offset.val < size parent

  field parent offset C := false
  field parent offset child := true
}

action AddRoot (_m : Mutator) (ptr : Ptr) {
  require phase = idle
  require is_allocated ptr
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

  -- is_allocated makes sure it's not blue or invalid
  -- then we just make sure that it's not black either,
  -- if it's black it means all its children have been visited
  -- so we don't want to do anything to it
  color P := if ( field_of curr_ptr P ) ∧ (is_allocated P) ∧ (color P != black) then gray else color P

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

  phase := sweep
}


action Sweep (_c : Collector) {
  require phase = sweep

  -- if the parent is white(unreachable), clear out its fields
  field P O C := if color P = white then false else field P O C

  -- everything white is blue now since it was unreachable
  color P := if color P = white then blue else color P
}

action CompleteSweep (_c : Collector) {
  require phase = sweep
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
  phase := idle
}


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
  ∀ ptr, roots ptr → is_allocated ptr

-- field invariants
invariant [fields_from_allocated]
  ∀ parent off child, field parent off child → is_allocated parent
invariant [fields_to_allocated]
  ∀ parent off child, field parent off child → is_allocated child
invariant [free_blocks_have_no_fields]
  ∀ parent off child, is_free parent → ¬ field parent off child

invariant [field_unique]
  ∀ parent off child1 child2,
    field parent off child1 ∧ field parent off child2 → child1 = child2
invariant [field_is_in_bounds]
  ∀ parent off child, field parent off child → off.val < size parent

-- Free blocks have a next pointer means the next pointer is also
-- free
invariant [free_block_next_wellformed]
  ∀ ptr, is_free ptr ∧ next ptr ≠ null_ptr → is_free (next ptr)

-- allocated block has no next ptr
invariant [allocated_block_next_unused]
  ∀ ptr, is_allocated ptr → next ptr = null_ptr

-- stop-the-world when doing GC(mark and sweep)
invariant [world_paused_during_gc] ∀ m , (phase != idle ∧ phase != gc_requested ) ->  world_paused m


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


invariant [roots_black_during_after_unreachables_sweeping]
    ∀ r, roots r ∧ phase = sweep -> color r = black

invariant [reachables_still_black_after_unreachables_sweeping]
  ∀ p off c,
    phase = sweep ∧ color p = black ∧ field p off c →
      color c = black


-- since we turn everything that was marked black(reachable) to white during sweep
-- Think there's a slight problem:
-- Say we have coalescing, then this may not hold exactly.. because we might merge stuff, so roots may not actually be valid.
-- TODO: coalescing
-- A way to state something useful during coalescing would be via a range thingy. In this case,
-- we could state that the r's value is in between a block (exists some p, r >= p ∧ p + p.size > r)
invariant [all_roots_white_after_sweep] ∀ r , phase = sweep_complete ∧ roots r -> color r = white

-- if a field is white, all it's children are also white
invariant [all_white_points_to_white_after_sweep] ∀ ptr child , phase = sweep_complete ∧ field_of ptr child ∧ color ptr = white ->  color child = white

#gen_spec


-- #model_check interpreted
--   { Mutator := Fin 1, Collector := Fin 1, Ptr := Fin 8, HeapSize := 4 }
--   { heap_start := (2 : Fin 8),
--     null_ptr := (0 : Fin 8),
--     ptrToAddr := fun p => p.val,
--     addrToPtr := fun n => Fin.ofNat 8 n }

#check RelationalTransitionSystem

-- #check_invariants

end VerifiedGc
