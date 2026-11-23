import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1003 : PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 13 := by
  refine ⟨{ gates := [
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 9]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 11]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 6]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 4]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 16]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [10, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 14]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 17]⟩], output := 20 }, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · intro x
    apply Bool.eq_iff_iff.mpr
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl_cons, List.foldl_nil, List.ofFn_succ, List.ofFn_zero,
      List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, PEqualNP.CircuitLowerBounds.GateOp.eval, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, id, Bool.and_true, Bool.or_false,
      Bool.and_eq_true, Bool.or_eq_true]
    grind (splits := 32)
