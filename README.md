# veil-gc

## Structure

- `VeilGc.lean` has the Veil formalization.
- `VeilGc/SoundAndComplete.lean` has the soundness implication proof with invariants from Veil as assumptions.
- `VeilGc/*VCs*.lean` : The files with VCs in their name are goals extracted from Veil with `#check_invariants`. 
    They are not in `VeilGc.lean` because there are more than 80 of them and adding them to the file makes it very slow.
- `check_invariants.png` shows the `#check_invariants` result
- `check_invariants.json` shows the result of `#check_invariants` extracted to json.

## Build Instructions

- `lake build` runs the Veil formalization.
- `lake build Veil/Basic.lean` runs all the theorems extracted from Veil. There are 9 sorries, all from `AllocateVCsSplit2`.


## Current State of the formalization

- There are 900 VCs, 820 are discharged by Veil automatically. Out of 80 left, 9 of them are sorried in `AllocateVCsSplit2.lean` file.
- Model checking with the currently commented out block takes `4-5` hours roughly.
- `#check_invariants` takes ~30 minutes.
