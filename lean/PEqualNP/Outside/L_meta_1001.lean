import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1001 : PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 16 := by
  refine ⟨{ gates := [
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 10]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 6]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 12]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 8]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 15]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [7, 17]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 5]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 19]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [21, 16]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [22, 18]⟩,
      ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [23, 20]⟩], output := 24 }, ?_, ?_, ?_⟩
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
