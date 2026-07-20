import MoserMacLeod.TableRows351_400

/-!
# Finite endpoint certificate

This module dispatches the eight independently compiled, proof-producing
certificate shards.  The mathematical proof imports this theorem and is
insulated from the generated row data.
-/

namespace MoserMacLeod

open Finset

/-- The exact bounded certificate. Each theorem in the dependency chain is an
ordinary proof term; no native evaluator is used. -/
theorem finite_endpoint_certificate (N : ℕ) (hN : N ∈ Icc 1 400) :
    endpointOK (squarefreeCountNat N) N ∧
      endpointOK (squarefreeCountNat N) (N + 1) := by
  simp only [mem_Icc] at hN
  rcases hN with ⟨hlo, hhi⟩
  by_cases h50 : N ≤ 50
  · exact finite_endpoint_certificate_001_050 N hlo h50
  by_cases h100 : N ≤ 100
  · exact finite_endpoint_certificate_051_100 N (by omega) h100
  by_cases h150 : N ≤ 150
  · exact finite_endpoint_certificate_101_150 N (by omega) h150
  by_cases h200 : N ≤ 200
  · exact finite_endpoint_certificate_151_200 N (by omega) h200
  by_cases h250 : N ≤ 250
  · exact finite_endpoint_certificate_201_250 N (by omega) h250
  by_cases h300 : N ≤ 300
  · exact finite_endpoint_certificate_251_300 N (by omega) h300
  by_cases h350 : N ≤ 350
  · exact finite_endpoint_certificate_301_350 N (by omega) h350
  · exact finite_endpoint_certificate_351_400 N (by omega) hhi

end MoserMacLeod
