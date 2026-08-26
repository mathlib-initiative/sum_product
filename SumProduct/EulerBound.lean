/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Euler-product bound for the Dedekind zeta function

Towards eliminating the `dedekindZeta_euler_le` axiom: we prove `ζ_K(2) ≤ ζ(2)^d` by showing the
coefficient `a_n = #{ideals of norm n}` is multiplicative and bounded by the `d`-fold divisor
function. This file builds that up.

* `idealCount K n` — the Dedekind-zeta coefficient `#{I : absNorm I = n}`.
* `idealCount_one` — `a_1 = 1`.
* `idealCount_mul_of_coprime` — multiplicativity (step 1, the crux).
* `idealCount_prime_pow_le` — the local bound `a_{p^k} ≤ C(d+k-1, k) = d_d(p^k)` (step 2), via an
  injection of the norm-`p^k` ideals into the `finsuppAntidiag` of the primes over `p`.
* `zeta_pow_apply_prime_pow` — `(ζ^d)(p^k) = C(d+k-1,k)`, the `d`-fold divisor at prime powers.
* `idealCount_le_zeta_pow` — the pointwise bound `a_n ≤ (ζ^d)(n)` for `n ≥ 1` (step 3), reducing to
  the prime powers by multiplicativity of both sides.
* `LSeriesSummable_and_LSeries_zeta_pow` — the L-series of `ζ^d` is summable and equals
  `riemannZeta^d` on `1 < re s` (steps 4–5), by iterated Dirichlet convolution.
-/

open scoped NumberField
open NumberField UniqueFactorizationMonoid

namespace SumProduct

variable {K : Type*} [Field K] [NumberField K]

/-- The Dedekind-zeta coefficient: the number of integral ideals of `𝓞 K` of norm `n`. -/
noncomputable def idealCount (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

/-- `a_1 = 1`: the only ideal of norm `1` is `⊤`. -/
lemma idealCount_one : idealCount K 1 = 1 := by
  rw [idealCount, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun I J => ?_⟩, ⟨⟨⊤, Ideal.absNorm_top⟩⟩⟩
  obtain ⟨I, hI⟩ := I
  obtain ⟨J, hJ⟩ := J
  simp only [Subtype.mk_eq_mk]
  rw [Ideal.absNorm_eq_one_iff.mp hI, Ideal.absNorm_eq_one_iff.mp hJ]

/-- Coprime norms imply coprime ideals: if `gcd(|I|, |J|) = 1` then `I + J = ⊤`. -/
private lemma isCoprime_of_coprime_absNorm {K : Type*} [Field K] [NumberField K]
    {I J : Ideal (𝓞 K)} (h : Nat.Coprime (Ideal.absNorm I) (Ideal.absNorm J)) : IsCoprime I J := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨M, hM, hIJM⟩ := Ideal.exists_le_maximal _ hne
  have hdI : Ideal.absNorm M ∣ Ideal.absNorm I :=
    Ideal.absNorm_dvd_absNorm_of_le (le_trans le_sup_left hIJM)
  have hdJ : Ideal.absNorm M ∣ Ideal.absNorm J :=
    Ideal.absNorm_dvd_absNorm_of_le (le_trans le_sup_right hIJM)
  exact hM.ne_top (Ideal.absNorm_eq_one_iff.mp (Nat.dvd_one.mp (h ▸ Nat.dvd_gcd hdI hdJ)))

/-- The product of `K`'s normalized factors recovers `K` (ideals have trivial units, so associated
ideals are equal). -/
private lemma prod_normalizedFactors_ideal {K : Type*} [Field K] [NumberField K]
    {I : Ideal (𝓞 K)} (hI : I ≠ 0) : (normalizedFactors I).prod = I :=
  associated_iff_eq.mp (prod_normalizedFactors hI)

/-- Splitting: an ideal `K` of norm `m*n` (`m,n` coprime, nonzero) factors as `I*J` with
`absNorm I = m`, `absNorm J = n`. -/
private lemma exists_split {K : Type*} [Field K] [NumberField K] {m n : ℕ}
    (hmn : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) {L : Ideal (𝓞 K)}
    (hL : Ideal.absNorm L = m * n) :
    ∃ I J : Ideal (𝓞 K), Ideal.absNorm I = m ∧ Ideal.absNorm J = n ∧ I * J = L := by
  have hL0 : L ≠ 0 := by
    intro h; rw [h, Ideal.zero_eq_bot, Ideal.absNorm_bot] at hL
    exact (mul_ne_zero hm hn) hL.symm
  classical
  set I : Ideal (𝓞 K) :=
    ((normalizedFactors L).filter (fun P => Nat.Coprime (Ideal.absNorm P) n)).prod with hIdef
  set J : Ideal (𝓞 K) :=
    ((normalizedFactors L).filter (fun P => ¬ Nat.Coprime (Ideal.absNorm P) n)).prod with hJdef
  have hsplit : (normalizedFactors L).filter (fun P => Nat.Coprime (Ideal.absNorm P) n)
      + (normalizedFactors L).filter (fun P => ¬ Nat.Coprime (Ideal.absNorm P) n)
      = normalizedFactors L := Multiset.filter_add_not _ _
  have hIJ : I * J = L := by
    rw [hIdef, hJdef, ← Multiset.prod_add, hsplit, prod_normalizedFactors_ideal hL0]
  have hnorm : Ideal.absNorm I * Ideal.absNorm J = m * n := by rw [← map_mul, hIJ, hL]
  -- `I`'s factors have norm coprime to `n`, so `absNorm I` is coprime to `n`.
  have hcopIn : Nat.Coprime (Ideal.absNorm I) n := by
    rw [hIdef, map_multiset_prod]
    refine Multiset.prod_induction (Nat.Coprime · n) _ (fun a b => Nat.Coprime.mul_left)
      (Nat.coprime_one_left n) ?_
    intro x hx
    simp only [Multiset.mem_map] at hx
    obtain ⟨P, hP, rfl⟩ := hx
    exact (Multiset.mem_filter.mp hP).2
  -- `J`'s factors have norm a prime power `q^j` with `q ∣ n`, hence coprime to `m`.
  have hcopMJ : Nat.Coprime m (Ideal.absNorm J) := by
    rw [hJdef, map_multiset_prod]
    refine Multiset.prod_induction (Nat.Coprime m ·) _ (fun a b => Nat.Coprime.mul_right)
      (Nat.coprime_one_right m) ?_
    intro x hx
    simp only [Multiset.mem_map] at hx
    obtain ⟨P, hP, rfl⟩ := hx
    have hPmem : P ∈ normalizedFactors L := Multiset.mem_of_mem_filter hP
    have hPnc : ¬ Nat.Coprime (Ideal.absNorm P) n := by
      have := (Multiset.mem_filter.mp hP).2; simpa using this
    have hPprime : Prime P := prime_of_normalized_factor P hPmem
    have hP0 : P ≠ ⊥ := hPprime.ne_zero
    have hPmax : P.IsMaximal := (Ideal.isPrime_of_prime hPprime).isMaximal hP0
    obtain ⟨q, j, hj, _, hq, hPq⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    rw [hPq] at hPnc ⊢
    have hqn : q ∣ n := by
      by_contra hqn
      exact hPnc ((Nat.coprime_pow_left_iff hj q n).mpr
        ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn))
    exact (Nat.Coprime.coprime_dvd_right hqn hmn).pow_right j
  have hIm : Ideal.absNorm I = m :=
    Nat.dvd_antisymm
      (hcopIn.dvd_of_dvd_mul_right ⟨_, hnorm.symm⟩)
      (hcopMJ.dvd_of_dvd_mul_right (by rw [hnorm]; exact dvd_mul_right m n))
  have hJn : Ideal.absNorm J = n := by
    have h2 : m * Ideal.absNorm J = m * n := hIm ▸ hnorm
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) h2
  exact ⟨I, J, hIm, hJn, hIJ⟩

/-- **Multiplicativity** of the ideal-counting function: for coprime `m, n`,
`a_{mn} = a_m · a_n`. The bijection is `(I, J) ↦ I·J` (norms multiply); surjectivity is
`exists_split`, injectivity uses that coprime norms give coprime ideals. -/
theorem idealCount_mul_of_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0) :
    idealCount K (m * n) = idealCount K m * idealCount K n := by
  rw [idealCount, idealCount, idealCount, ← Nat.card_prod]
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n} =>
      (⟨p.1.1 * p.2.1, by rw [map_mul, p.1.2, p.2.2]⟩ :
        {L : Ideal (𝓞 K) // Ideal.absNorm L = m * n})) ⟨?_, ?_⟩).symm
  · rintro ⟨⟨I, hI⟩, ⟨J, hJ⟩⟩ ⟨⟨I', hI'⟩, ⟨J', hJ'⟩⟩ heq
    simp only [Subtype.mk_eq_mk] at heq
    have hI0 : I ≠ 0 := fun h => hm (by rw [← hI, h, Ideal.zero_eq_bot, Ideal.absNorm_bot])
    have hcop : IsCoprime I J' := isCoprime_of_coprime_absNorm (by rw [hI, hJ']; exact hmn)
    have hcop' : IsCoprime I' J := isCoprime_of_coprime_absNorm (by rw [hI', hJ]; exact hmn)
    have hII' : I = I' :=
      dvd_antisymm (hcop.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right I J))
        (hcop'.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right I' J'))
    have hJJ' : J = J' := by
      rw [hII'] at heq; exact mul_left_cancel₀ (hII' ▸ hI0) heq
    simp only [Prod.mk_inj, Subtype.mk_eq_mk]; exact ⟨hII', hJJ'⟩
  · rintro ⟨L, hL⟩
    obtain ⟨I, J, hI, hJ, hIJ⟩ := exists_split hmn hm hn hL
    exact ⟨(⟨I, hI⟩, ⟨J, hJ⟩), by simp only [Subtype.mk_eq_mk]; exact hIJ⟩

/-- Every prime factor of an ideal of norm `p^k` (`p` prime) lies over `p`, i.e. belongs to the
finite set `primesOverFinset (p) (𝓞 K)`. (The norm of the factor divides `p^k`, hence is a power
of `p`, so `p` divides it, and `exists_isMaximal_dvd_of_dvd_absNorm'` exhibits the factor itself as
a maximal ideal over `p`.) -/
private lemma factor_mem_primesOverFinset {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (hp : p.Prime) {k : ℕ} {I 𝔭 : Ideal (𝓞 K)} (hI : Ideal.absNorm I = p ^ k)
    (h𝔭 : 𝔭 ∈ normalizedFactors I) :
    𝔭 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) := by
  have hprime : Prime 𝔭 := prime_of_normalized_factor 𝔭 h𝔭
  have hmax : 𝔭.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  have hdvd : 𝔭 ∣ I := dvd_of_mem_normalizedFactors h𝔭
  have hle : I ≤ 𝔭 := Ideal.dvd_iff_le.mp hdvd
  have hnorm_dvd : Ideal.absNorm 𝔭 ∣ Ideal.absNorm I := Ideal.absNorm_dvd_absNorm_of_le hle
  obtain ⟨q, j, hj, _, hq, hQq⟩ := Ideal.exists_prime_and_absNorm_eq_pow 𝔭
  -- `q^j = |𝔭| ∣ p^k`, so the prime `q` equals `p`.
  have hqdvd : q ∣ p ^ k := by
    rw [hQq, hI] at hnorm_dvd; exact dvd_trans (dvd_pow_self q hj.ne') hnorm_dvd
  have hpq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqdvd)
  have hpdvd : (p : ℕ) ∣ Ideal.absNorm 𝔭 := by
    rw [hQq, hpq]; exact dvd_pow_self p hj.ne'
  obtain ⟨P, hPmax, hPunder, hPdvd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp 𝔭 hpdvd
  -- `P ∣ 𝔭` with both maximal forces `P = 𝔭`, so `𝔭` lies over `p`.
  have hP𝔭 : P = 𝔭 := (hmax.eq_of_le hPmax.ne_top (Ideal.dvd_iff_le.mp hPdvd)).symm
  rw [hP𝔭] at hPunder
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hpMax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ).isMaximal (by simpa using hpZ.ne_zero)
  have hLO : 𝔭.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPunder.symm⟩
  exact (IsDedekindDomain.mem_primesOverFinset_iff (by simpa using hpZ.ne_zero) (𝓞 K)).mpr
    ⟨Ideal.isPrime_of_prime hprime, hLO⟩

set_option maxHeartbeats 800000 in
-- The factorization-indexed injection into a `finsuppAntidiag`, with `Finsupp.indicator` over the
-- (let-bound) `primesOverFinset`, needs elaboration headroom beyond the default.
/-- **Local bound** (step 2): the number of ideals of norm `p^k` is at most the `d`-fold divisor
value `d_d(p^k) = C(d+k-1, k)` (`d = [K:ℚ]`). Each such ideal factors uniquely into primes over `p`
(at most `d` of them, `card_primesOverFinset_le_finrank`); recording, for each prime `𝔭` over `p`,
the product `v_𝔭(I)·f_𝔭` of its multiplicity and inertia degree gives an injection into the
`finsuppAntidiag` of total `k` (the norm gives `∑ v_𝔭 f_𝔭 = k`), counted by `multichoose`. -/
lemma idealCount_prime_pow_le {K : Type*} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (k : ℕ) :
    idealCount K (p ^ k) ≤ Nat.multichoose (Module.finrank ℚ K) k := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  haveI hpMax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ).isMaximal (by simpa using hpZ.ne_zero)
  have hpb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hpZ.ne_zero
  set G := IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) with hG
  have hGcard : G.card ≤ Module.finrank ℚ K :=
    Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hpb
  -- For `𝔭 ∈ G`: it lies over `p`, has positive inertia degree, and norm `p^{f_𝔭}`.
  have hLO : ∀ 𝔭 ∈ G, 𝔭.LiesOver (Ideal.span {(p : ℤ)}) ∧ 𝔭.IsPrime :=
    fun 𝔭 h𝔭 => ⟨((IsDedekindDomain.mem_primesOverFinset_iff hpb (𝓞 K)).mp h𝔭).2,
      ((IsDedekindDomain.mem_primesOverFinset_iff hpb (𝓞 K)).mp h𝔭).1⟩
  have hfpos : ∀ 𝔭 ∈ G, 0 < (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨hlo, hpr⟩ := hLO 𝔭 h𝔭
    exact Nat.pos_of_ne_zero (Ideal.inertiaDeg'_ne_zero _ _)
  have hnorm𝔭 : ∀ 𝔭 ∈ G, Ideal.absNorm 𝔭 = p ^ ((Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭) := by
    intro 𝔭 h𝔭
    obtain ⟨hlo, hpr⟩ := hLO 𝔭 h𝔭
    have := Ideal.absNorm_eq_pow_inertiaDeg 𝔭 hpZ
    simpa using this
  -- The injection `I ↦ (𝔭 ↦ v_𝔭(I)·f_𝔭)` supported on `G`.
  set Φ : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} → (Ideal (𝓞 K) →₀ ℕ) :=
    fun I => Finsupp.indicator G
      (fun 𝔭 _ => (normalizedFactors I.1).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭) with hΦ
  -- All prime factors of `I` (norm `p^k`) lie in `G`, hence `count = 0` off `G`.
  have hcount_off : ∀ (I : Ideal (𝓞 K)), Ideal.absNorm I = p ^ k →
      ∀ 𝔭 ∉ G, (normalizedFactors I).count 𝔭 = 0 := by
    intro I hI 𝔭 h𝔭
    by_contra h
    exact h𝔭 (factor_mem_primesOverFinset hp hI (Multiset.count_pos.mp (Nat.pos_of_ne_zero h)))
  -- The key norm identity: `∑_{𝔭∈G} v_𝔭(I)·f_𝔭 = k`.
  have hsum : ∀ (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k}),
      ∑ 𝔭 ∈ G, (normalizedFactors I.1).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭 = k := by
    rintro ⟨I, hI⟩
    have hI0 : I ≠ 0 := by
      rintro rfl
      rw [Ideal.zero_eq_bot, Ideal.absNorm_bot] at hI
      exact (pow_ne_zero k hp.pos.ne') hI.symm
    have habs : (Multiset.map Ideal.absNorm (normalizedFactors I)).prod = Ideal.absNorm I := by
      rw [← map_multiset_prod, prod_normalizedFactors_ideal hI0]
    have step1 : ∀ 𝔭 ∈ G, p ^ ((normalizedFactors I).count 𝔭 *
        (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭) = Ideal.absNorm 𝔭 ^ (normalizedFactors I).count 𝔭 := by
      intro 𝔭 h𝔭
      rw [hnorm𝔭 𝔭 h𝔭, ← pow_mul, mul_comm]
    have hsub : (normalizedFactors I).toFinset ⊆ G :=
      fun 𝔭 h𝔭 => factor_mem_primesOverFinset hp hI (Multiset.mem_toFinset.mp h𝔭)
    have hone : ∀ 𝔭 ∈ G, 𝔭 ∉ (normalizedFactors I).toFinset →
        Ideal.absNorm 𝔭 ^ (normalizedFactors I).count 𝔭 = 1 := by
      intro 𝔭 _ h𝔭
      rw [Multiset.count_eq_zero.mpr (fun hmem => h𝔭 (Multiset.mem_toFinset.mpr hmem)), pow_zero]
    have hpow : p ^ (∑ 𝔭 ∈ G, (normalizedFactors I).count 𝔭 *
        (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭) = p ^ k :=
      calc p ^ (∑ 𝔭 ∈ G, (normalizedFactors I).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭)
          = ∏ 𝔭 ∈ G, p ^ ((normalizedFactors I).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭) :=
            (Finset.prod_pow_eq_pow_sum G _ p).symm
        _ = ∏ 𝔭 ∈ G, Ideal.absNorm 𝔭 ^ (normalizedFactors I).count 𝔭 := Finset.prod_congr rfl step1
        _ = ∏ 𝔭 ∈ (normalizedFactors I).toFinset, Ideal.absNorm 𝔭 ^ (normalizedFactors I).count 𝔭 :=
            (Finset.prod_subset hsub hone).symm
        _ = (Multiset.map Ideal.absNorm (normalizedFactors I)).prod :=
            (Finset.prod_multiset_map_count _ _).symm
        _ = Ideal.absNorm I := habs
        _ = p ^ k := hI
    exact Nat.pow_right_injective hp.two_le hpow
  -- `Φ` lands in the antidiagonal.
  have hval : ∀ (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k}) 𝔭, 𝔭 ∈ G →
      (Φ I) 𝔭 = (normalizedFactors I.1).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭 := by
    intro I 𝔭 h𝔭
    simp only [hΦ]
    exact Finsupp.indicator_of_mem h𝔭 _
  have hsupp : ∀ (I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k}), (Φ I).support ⊆ G := by
    intro I
    simp only [hΦ]
    exact Finsupp.support_indicator_subset G _
  have hmem : ∀ I, Φ I ∈ G.finsuppAntidiag k := by
    intro I
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, hsupp I⟩
    change ∑ 𝔭 ∈ G, (Φ I) 𝔭 = k
    rw [Finset.sum_congr rfl (hval I)]
    exact hsum I
  -- `Φ` is injective.
  have hinj : Function.Injective Φ := by
    rintro ⟨I, hI⟩ ⟨J, hJ⟩ hIJ
    have hI0 : I ≠ 0 := by
      rintro rfl; rw [Ideal.zero_eq_bot, Ideal.absNorm_bot] at hI
      exact pow_ne_zero k hp.pos.ne' hI.symm
    have hJ0 : J ≠ 0 := by
      rintro rfl; rw [Ideal.zero_eq_bot, Ideal.absNorm_bot] at hJ
      exact pow_ne_zero k hp.pos.ne' hJ.symm
    have hcounts : normalizedFactors I = normalizedFactors J := by
      ext 𝔭
      by_cases h𝔭 : 𝔭 ∈ G
      · have key : (normalizedFactors I).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭
            = (normalizedFactors J).count 𝔭 * (Ideal.span {(p : ℤ)}).inertiaDeg' 𝔭 := by
          have h2 := DFunLike.congr_fun hIJ 𝔭
          simpa only [hΦ, Finsupp.indicator_of_mem h𝔭] using h2
        exact Nat.eq_of_mul_eq_mul_right (hfpos 𝔭 h𝔭) key
      · rw [hcount_off I hI 𝔭 h𝔭, hcount_off J hJ 𝔭 h𝔭]
    have : I = J := by
      rw [← prod_normalizedFactors_ideal hI0, ← prod_normalizedFactors_ideal hJ0, hcounts]
    simpa using this
  -- Counting.
  calc idealCount K (p ^ k)
      = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p ^ k} := rfl
    _ ≤ Nat.card ↥(G.finsuppAntidiag k) :=
        Nat.card_le_card_of_injective (fun I => ⟨Φ I, hmem I⟩)
          (fun a b h => hinj (Subtype.mk_eq_mk.mp h))
    _ = (G.finsuppAntidiag k).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.multichoose G.card k := Finset.card_finsuppAntidiag_nat_eq_multichoose k
    _ ≤ Nat.multichoose (Module.finrank ℚ K) k := by
        rw [Nat.multichoose_eq, Nat.multichoose_eq]
        exact Nat.choose_le_choose k (Nat.sub_le_sub_right (Nat.add_le_add_right hGcard k) 1)

open scoped ArithmeticFunction.zeta in
/-- The `d`-fold divisor function `ζ^d` (Dirichlet convolution power) at a prime power:
`(ζ^d)(p^k) = C(d+k-1, k) = multichoose d k`. Proved by induction on `d`: the convolution
`(ζ^d * ζ)(p^k) = ∑_{i≤k} (ζ^d)(p^i)` telescopes by the hockey-stick identity for `multichoose`. -/
lemma zeta_pow_apply_prime_pow {p : ℕ} (hp : p.Prime) (d k : ℕ) :
    (ζ ^ d : ArithmeticFunction ℕ) (p ^ k) = Nat.multichoose d k := by
  induction d generalizing k with
  | zero =>
    rw [pow_zero, ArithmeticFunction.one_apply]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [if_neg (fun h => by simp [hp.ne_one, hk.ne'] at h),
        Nat.multichoose_eq, Nat.choose_eq_zero_of_lt (by omega)]
  | succ d ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun a b => (ζ ^ d : ArithmeticFunction ℕ) a * ζ b),
      Nat.sum_divisors_prime_pow hp]
    have hz : ∀ i ∈ Finset.range (k + 1),
        (ζ ^ d : ArithmeticFunction ℕ) (p ^ i) * ζ (p ^ k / p ^ i) = Nat.multichoose d i := by
      intro i hi
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi
      rw [ih i, Nat.pow_div hi hp.pos,
        ArithmeticFunction.zeta_apply_ne (pow_ne_zero (k - i) hp.pos.ne'), mul_one]
    rw [Finset.sum_congr rfl hz]
    rw [Nat.sum_range_multichoose, Nat.multichoose_eq, show d + 1 + k - 1 = k + d by omega,
      ← Nat.choose_symm (Nat.le_add_right k d), Nat.add_sub_cancel_left]

/-- `idealCount` packaged as an arithmetic function (vanishing at `0`, agreeing with the genuine
coefficient at every `n ≥ 1`). -/
noncomputable def idealCountArith (K : Type*) [Field K] [NumberField K] : ArithmeticFunction ℕ where
  toFun n := if n = 0 then 0 else idealCount K n
  map_zero' := if_pos rfl

@[simp] lemma idealCountArith_apply_ne {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    idealCountArith K n = idealCount K n := if_neg hn

lemma isMultiplicative_idealCountArith : (idealCountArith K).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [idealCount_one], fun {m n} hm hn hmn => ?_⟩
  simp only [idealCountArith_apply_ne hm, idealCountArith_apply_ne hn,
    idealCountArith_apply_ne (mul_ne_zero hm hn)]
  exact idealCount_mul_of_coprime hmn hm hn

lemma isMultiplicative_zeta_pow (d : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d).IsMultiplicative := by
  induction d with
  | zero => rw [pow_zero]; exact ArithmeticFunction.isMultiplicative_one
  | succ d ih => rw [pow_succ]; exact ih.mul ArithmeticFunction.isMultiplicative_zeta

/-- **Step 3**: the pointwise divisor bound `a_n ≤ d_d(n)` for `n ≥ 1`. Both `a` and the `d`-fold
divisor `ζ^d` are multiplicative, so the bound reduces (`multiplicative_factorization`) to the prime
powers, where it is `idealCount_prime_pow_le` together with `zeta_pow_apply_prime_pow`. -/
lemma idealCount_le_zeta_pow {K : Type*} [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    idealCount K n
      ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ (Module.finrank ℚ K)) n := by
  rw [← idealCountArith_apply_ne (K := K) hn,
    isMultiplicative_idealCountArith.multiplicative_factorization _ hn,
    (isMultiplicative_zeta_pow _).multiplicative_factorization _ hn,
    Finsupp.prod, Finsupp.prod]
  apply Finset.prod_le_prod'
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
  rw [idealCountArith_apply_ne (pow_ne_zero _ hpp.pos.ne'), zeta_pow_apply_prime_pow hpp]
  exact idealCount_prime_pow_le hpp _

open scoped LSeries.notation in
open ArithmeticFunction in
/-- The L-series of the `d`-fold divisor function `ζ^d` is summable and equals the `d`-th power of
the Riemann zeta function on `1 < re s`. Induction on `d` via `LSeries_mul'`. -/
lemma LSeriesSummable_and_LSeries_zeta_pow {s : ℂ} (hs : 1 < s.re) (d : ℕ) :
    LSeriesSummable (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℂ)) s ∧
      LSeries (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℂ)) s
        = riemannZeta s ^ d := by
  -- Work in `ArithmeticFunction ℂ`: `Z = ↑ζ`, and `↑(ζ^m) = Z^m`.
  set Z : ArithmeticFunction ℂ :=
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) with hZdef
  have hcoeAF : ∀ m : ℕ,
      (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ m : ArithmeticFunction ℕ)
        : ArithmeticFunction ℂ) = Z ^ m := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero]; exact natCoe_one
    | succ m ih => rw [pow_succ, pow_succ, natCoe_mul, ih, hZdef]
  have hcoe : ∀ m : ℕ, (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ m) n : ℂ))
      = ↗(Z ^ m) := fun m => funext fun n => by rw [← hcoeAF m, natCoe_apply]
  have hZsum : LSeriesSummable (↗Z) s := by rw [hZdef]; exact LSeriesSummable_zeta_iff.mpr hs
  have hZS : LSeries (↗Z) s = riemannZeta s := by rw [hZdef]; exact LSeries_zeta_eq_riemannZeta hs
  have hδ : LSeriesSummable (↗(1 : ArithmeticFunction ℂ)) s := by
    rw [one_eq_delta]
    refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
    simp only [Finset.mem_singleton] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [LSeries.term]
    · rw [LSeries.term_of_ne_zero hpos.ne']; simp [LSeries.delta, hn]
  suffices h : ∀ m, LSeriesSummable (↗(Z ^ m)) s ∧ LSeries (↗(Z ^ m)) s = riemannZeta s ^ m by
    rw [hcoe d]; exact h d
  intro m
  induction m with
  | zero =>
    refine ⟨by rw [pow_zero]; exact hδ, ?_⟩
    rw [pow_zero, pow_zero, one_eq_delta, LSeries_delta]; exact Pi.one_apply s
  | succ m ih =>
    refine ⟨by rw [pow_succ]; exact LSeriesSummable_mul ih.1 hZsum, ?_⟩
    rw [pow_succ, LSeries_mul' ih.1 hZsum, ih.2, hZS, pow_succ]

/-- **Step 6**: `ζ_K(2) ≤ ζ(2)^d ≤ 2^d`. Termwise, `(dedekindZeta K 2).re = ∑ a_n/n²` (the
coefficients are real and nonnegative); the pointwise bound `a_n ≤ d_d(n)` gives
`∑ a_n/n² ≤ ∑ d_d(n)/n² = ζ(2)^d = (π²/6)^d`, and `π²/6 ≤ 2`. This matches the `s = 2`
specialization of the (now redundant) `dedekindZeta_euler_le` axiom. -/
theorem dedekindZeta_two_re_le {K : Type*} [Field K] [NumberField K] :
    (NumberField.dedekindZeta K (2 : ℂ)).re ≤ 2 ^ Module.finrank ℚ K := by
  set d := Module.finrank ℚ K with hd
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  obtain ⟨hbsum, hbeq⟩ := LSeriesSummable_and_LSeries_zeta_pow h2 d
  set ra : ℕ → ℝ := fun n => (idealCount K n : ℝ) / (n : ℝ) ^ 2 with hra
  set rb : ℕ → ℝ :=
    fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℝ) / (n : ℝ) ^ 2 with hrb
  -- The L-series term at `s = 2` is the (cast of the) real coefficient.
  have htermA : ∀ n, LSeries.term (fun n => (idealCount K n : ℂ)) 2 n = (ra n : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, hra]
    · rw [LSeries.term_of_ne_zero hn.ne', hra, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
        Complex.cpow_natCast]
      push_cast; ring
  have htermB : ∀ n, LSeries.term
      (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℂ)) 2 n
        = (rb n : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term, hrb]
    · rw [LSeries.term_of_ne_zero hn.ne', hrb, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
        Complex.cpow_natCast]
      push_cast; ring
  -- Real summability of both coefficient series, and the pointwise bound.
  have hrbsum : Summable rb := by
    have h : Summable (LSeries.term
        (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℂ)) 2) := hbsum
    exact (Complex.summable_ofReal).mp (h.congr htermB)
  have hra_le : ∀ n, ra n ≤ rb n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hra, hrb]
    · have hle : (idealCount K n : ℝ)
          ≤ (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℝ) := by
        exact_mod_cast idealCount_le_zeta_pow hn.ne'
      simp only [hra, hrb]; gcongr
  have hrasum : Summable ra := Summable.of_nonneg_of_le (fun n => by positivity) hra_le hrbsum
  have hasum : LSeriesSummable (fun n => (idealCount K n : ℂ)) 2 := by
    have h1 : Summable (fun n => ((ra n : ℝ) : ℂ)) := (Complex.summable_ofReal).mpr hrasum
    exact h1.congr (fun n => (htermA n).symm)
  -- `(dedekindZeta K 2).re = ∑ a_n/n²`.
  have hzeta : (NumberField.dedekindZeta K (2 : ℂ)).re = ∑' n, ra n := by
    change (∑' n, LSeries.term (fun n => (idealCount K n : ℂ)) 2 n).re = ∑' n, ra n
    rw [Complex.re_tsum hasum]
    exact tsum_congr fun n => by rw [htermA n, Complex.ofReal_re]
  -- `∑ d_d(n)/n² = (π²/6)^d`.
  have hbre : (∑' n, rb n) = (Real.pi ^ 2 / 6) ^ d := by
    have h : (((∑' n, rb n : ℝ)) : ℂ) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) ^ d := by
      rw [Complex.ofReal_tsum]
      calc ∑' n, ((rb n : ℝ) : ℂ)
          = LSeries (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ d) n : ℂ)) 2 :=
            tsum_congr fun n => (htermB n).symm
        _ = riemannZeta 2 ^ d := hbeq
        _ = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) ^ d := by rw [riemannZeta_two]; push_cast; ring
    exact_mod_cast h
  rw [hzeta]
  calc ∑' n, ra n
      ≤ ∑' n, rb n := Summable.tsum_le_tsum hra_le hrasum hrbsum
    _ = (Real.pi ^ 2 / 6) ^ d := hbre
    _ ≤ 2 ^ d := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith [Real.pi_lt_d2, Real.pi_pos]

end SumProduct
