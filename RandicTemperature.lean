module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

public section

namespace RandicTemperature

open Finset SimpleGraph
open scoped BigOperators

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Half the sum of edge weights over ordered adjacent vertex pairs. -/
noncomputable def randic : ℝ :=
  (∑ u, ∑ v, if G.Adj u v then
    1 / Real.sqrt ((G.degree u : ℝ) * G.degree v) else 0) / 2

/-- Fajtlowicz's vertex temperature, with graph order n and degree d. -/
noncomputable def temperature (v : Fin n) : ℝ := (G.degree v : ℝ) / (n - (G.degree v : ℝ))

noncomputable def score (v : Fin n) : ℝ := (2 : ℝ) ^ G.degree v / temperature G v

noncomputable def maxScore (hn : 2 ≤ n) : ℝ :=
  univ.sup' ⟨⟨0, by omega⟩, mem_univ _⟩ (score G)

/-- The weight of an undirected edge is independent of its choice of orientation. -/
noncomputable def edgeWeight (e : Sym2 (Fin n)) : ℝ :=
  Sym2.lift ⟨fun u v => 1 / Real.sqrt ((G.degree u : ℝ) * G.degree v),
    fun u v => by simp [mul_comm]⟩ e

/-- The ordered-pair sum agrees with the author's sum over undirected edges. -/
theorem randic_eq_edge_sum : randic G = ∑ e ∈ G.edgeFinset, edgeWeight G e := by
  let adjPair := fun p : Fin n × Fin n => G.Adj p.1 p.2
  have hdart : (∑ d : G.Dart, edgeWeight G d.edge) =
      ∑ p ∈ (univ.filter adjPair), edgeWeight G s(p.1, p.2) := by
    refine Finset.sum_bij' (fun d _ => (d.fst, d.snd))
      (fun xy h => ⟨xy, (mem_filter.mp h).2⟩) ?_ ?_ ?_ ?_ ?_
    · exact fun d _ => mem_filter.mpr ⟨mem_univ _, d.adj⟩
    · exact fun _ _ => mem_univ _
    · intro d _; rfl
    · intro xy _; rfl
    · intro d _; rfl
  have hsum : (∑ d : G.Dart, edgeWeight G d.edge) =
      2 * ∑ e ∈ G.edgeFinset, edgeWeight G e := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := SimpleGraph.Dart.edge)
      (t := G.edgeFinset) (fun d _ => G.mem_edgeFinset.mpr d.edge_mem), Finset.mul_sum]
    apply sum_congr rfl
    intro e he
    calc
      _ = ∑ _d ∈ univ.filter (fun d : G.Dart => d.edge = e), edgeWeight G e :=
        sum_congr rfl fun d hd => by rw [(mem_filter.mp hd).2]
      _ = _ := by simp [G.dart_edge_fiber_card e (G.mem_edgeFinset.mp he)]
  rw [Finset.sum_filter, Fintype.sum_prod_type] at hdart
  change (∑ d : G.Dart, edgeWeight G d.edge) =
    ∑ u, ∑ v, if G.Adj u v then 1 / Real.sqrt ((G.degree u : ℝ) * G.degree v) else 0 at hdart
  rw [randic.eq_def, ← hdart, hsum]
  ring

private theorem edge_amgm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * (1 / Real.sqrt (a * b)) ≤ 1 / a + 1 / b := by
  have hs (z : ℝ) (hz : 0 < z) : (1 / Real.sqrt z) ^ 2 = 1 / z := by
    rw [div_pow, Real.sq_sqrt hz.le, one_pow]
  rw [Real.sqrt_mul ha.le, ← hs a ha, ← hs b hb]
  have h := sq_nonneg (1 / Real.sqrt a - 1 / Real.sqrt b)
  rw [← one_div_mul_one_div]
  nlinarith

private theorem row_inv (u : Fin n) (hu : 0 < G.degree u) :
    (∑ v, if G.Adj u v then 1 / (G.degree u : ℝ) else 0) = 1 := by
  rw [← Finset.sum_filter]
  rw [← G.neighborFinset_eq_filter, Finset.sum_const, G.card_neighborFinset_eq_degree]
  have h : (G.degree u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
  simp [nsmul_eq_mul, h]

/-- The classic upper bound, proved by applying AM–GM on each edge. -/
theorem two_mul_randic_le_order (hdeg : ∀ v, 0 < G.degree v) : 2 * randic G ≤ n := by
  let F : Fin n → Fin n → ℝ := fun u v => if G.Adj u v then 1 / (G.degree u : ℝ) else 0
  have hF : (∑ u, ∑ v, F u v) = (n : ℝ) := by
    calc
      _ = ∑ _ : Fin n, (1 : ℝ) := Finset.sum_congr rfl fun u _ => row_inv G u (hdeg u)
      _ = _ := by simp
  have hFt : (∑ u, ∑ v, F v u) = (n : ℝ) := by rw [Finset.sum_comm]; exact hF
  have h (u v : Fin n) :
      2 * (if G.Adj u v then 1 / Real.sqrt ((G.degree u : ℝ) * G.degree v) else 0)
        ≤ F u v + F v u := by
    by_cases huv : G.Adj u v
    · simpa [F, huv, huv.symm] using
        edge_amgm (G.degree u) (G.degree v) (by exact_mod_cast hdeg u) (by exact_mod_cast hdeg v)
    · have hvu : ¬G.Adj v u := fun h => huv h.symm
      simp [F, huv, hvu]
  have total := Finset.sum_le_sum (s := (univ : Finset (Fin n))) (fun u _ =>
    Finset.sum_le_sum (s := (univ : Finset (Fin n))) (fun v _ => h u v))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hF, hFt] at total
  unfold randic
  linarith

private theorem degree_arithmetic (d : ℕ) : 2 * d * (d+1) ≤ 3 * 2^d := by
  by_cases h : d < 2
  · interval_cases d <;> decide
  have hd : 2 ≤ d := by omega
  clear h
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
    rw [pow_succ]
    nlinarith [Nat.mul_le_mul_right (d+1) hd]

private theorem scalar (d n : ℕ) (hd : 0 < d) (hdn : d < n) :
    2 * (n : ℝ) ≤ 3 * ((2 : ℝ)^d / ((d : ℝ) / ((n : ℝ)-d))) := by
  have h : (2:ℝ)*d*(d+1) ≤ 3*(2:ℝ)^d := by exact_mod_cast degree_arithmetic d
  have hgap : (d : ℝ) + 1 ≤ n := by exact_mod_cast (show d+1 ≤ n by omega)
  have hpos : (0:ℝ)<d := by exact_mod_cast hd
  rw [div_div_eq_mul_div]
  rw [← mul_div_assoc, le_div_iff₀ hpos]
  have hdg : (n : ℝ) ≤ (d + 1 : ℝ) * (n-d) := by
    nlinarith [mul_nonneg (show (0:ℝ) ≤ (n : ℝ)-d-1 by linarith) hpos.le]
  nlinarith [mul_le_mul_of_nonneg_left hdg hpos.le,
    mul_le_mul_of_nonneg_right h (by linarith : (0:ℝ)≤(n:ℝ)-d)]

/-- The strengthened estimate holds at every vertex. -/
theorem pointwise_bound (hn : 2 ≤ n) (hc : G.Connected) (v : Fin n) :
    4 * randic G ≤ 3 * score G v := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hdeg (u : Fin n) : 0 < G.degree u := by
    exact hc.preconnected.degree_pos_of_nontrivial u
  have h₁ := two_mul_randic_le_order G hdeg
  have h₂ := scalar (G.degree v) n (hdeg v) (by simpa using G.degree_lt_card_verts v)
  change 4 * randic G ≤ 3 * ((2:ℝ)^G.degree v / ((G.degree v : ℝ) / ((n:ℝ)-G.degree v)))
  linarith

/-- Duhamel–Cazenave's original corpus item, retaining the maximum over vertices. -/
theorem conjecture_430943 (hn : 2 ≤ n) (hc : G.Connected) : randic G ≤ maxScore G hn := by
  let v : Fin n := ⟨0, by omega⟩
  have hm : score G v ≤ maxScore G hn := Finset.le_sup' (score G) (Finset.mem_univ v)
  have hp := pointwise_bound G hn hc v
  have hnon : 0 ≤ randic G := by unfold randic; positivity
  linarith

/-- The sharp ratio is attained on the triangle:
its Randić index is 3/2 and each vertex score is 2. -/
theorem triangle_values :
    randic (completeGraph (Fin 3)) = 3 / 2 ∧
      maxScore (completeGraph (Fin 3)) (by decide) = 2 := by
  have hs (v : Fin 3) : score (completeGraph (Fin 3)) v = 2 := by
    norm_num [score, temperature]
  constructor
  · norm_num [randic, Fin.sum_univ_three, SimpleGraph.top_adj]
  · unfold maxScore
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun u _ => (hs u).le
    · simpa only [hs (0 : Fin 3)] using
        (Finset.le_sup' (score (completeGraph (Fin 3))) (Finset.mem_univ (0 : Fin 3)))

/-- Among bounds of the form R ≤ c·maxScore valid on the full class, 3/4 is optimal. -/
theorem optimal_constant (c : ℝ) :
    (∀ (n : ℕ) (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
       G.Connected → randic G ≤ c * maxScore G hn) ↔ 3 / 4 ≤ c := by
  constructor
  · intro h
    have ht := h 3 (by decide) (completeGraph (Fin 3)) (by simp)
    rw [triangle_values.1, triangle_values.2] at ht
    linarith
  · intro hc n hn G _ hG
    let v : Fin n := ⟨0, by omega⟩
    have hp := pointwise_bound G hn hG v
    have hm : score G v ≤ maxScore G hn := Finset.le_sup' (score G) (mem_univ v)
    have hnon : 0 ≤ randic G := by unfold randic; positivity
    have hmax : 0 ≤ maxScore G hn := by linarith
    have := mul_le_mul_of_nonneg_right hc hmax
    linarith

/-- The same conjecture with precisely one summand per undirected edge. -/
theorem conjecture_430943_edge_form (hn : 2 ≤ n) (hc : G.Connected) :
    (∑ e ∈ G.edgeFinset, edgeWeight G e) ≤ maxScore G hn := by
  rw [← randic_eq_edge_sum]
  exact conjecture_430943 G hn hc

#print axioms conjecture_430943_edge_form
#print axioms conjecture_430943
#print axioms pointwise_bound
#print axioms optimal_constant

end RandicTemperature
