/-
Part of this repository. MIT OR Apache-2.0; see AGENTS.md.

The EIP's PCS openings of several sizes as one Fiat-Shamir family: `Union.lean`'s construction (the size's
index read in unary before the statement, adapted from leanerVM `mumbai`'s `anyProgram`, `leanVmSeeds`,
`anyCert`, https://github.com/Verified-zkEVM/leanerVM, commit 6175f1a0, MIT OR Apache-2.0) on
`PcsClaim.lean`'s seedings, and `Exact.lean`'s `roots_sound` with the statements' roots read through
their claims.
-/
import WhirBridge.Pcs
import WhirBridge.Union

/-!
# PCS openings of several sizes, charged once

A protocol that opens several PCS claims (`crates/pcs_claim`) of different sizes `n` (π1: `C1`'s
`2^27` words, `C2`'s `2^26`, the setup's `2^23`) charges their Fiat-Shamir doom once per query, as
statements of one family, at the per-group bound `ε` the deployed codes meet at every size:

* **`PcsShape ε`**: a size `n` of version 1 (`15 ≤ n ≤ 28`), whose deployed codes meet `ε` above the
  batching lead, and the opening's query count `QO`; **`PcsShapes ε`** a list of them of distinct
  sizes.
* **The union family**: statements `Σ j, Claim1 n_j`; the program reads the index in unary, then
  size `j`'s program (`famProgram (stacking n_j)`); a statement's root is the index's reads then its two
  claims' (`f(z) = ood`, `f(point) = value`); the seeding is the claim's own (`seed1`: the IV
  `keccak256(PCS_claim)`, which names `n` and every field). The roots name only the claims, not the
  commitment's root, so the certificate is built on the claims' statements (`PUSt`, prefix-free) and
  the seedings read through them (`roots_sound_map`).
* **`pcs_union_sound`**: an adversary of at most `QA` queries that outputs a size's index, a claim of
  that size and a proof makes `verify_claim` accept while every candidate of the word extracted for
  the claim's root violates `f(z) = ood` or `f(point) = value` with probability at most
  `(QA + QV) · (ε + 5 (QA + QV) / 2^256)`, `QV` above every size's `QO`.
-/

namespace WhirBridge.Pcs

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.Rom
open LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd.Sound (wordE kNat kNat_ofBits limb_wordE reachable_of_after_reads
  boundary_map_read grindBits_map_read commits_map_read commitStack_after_ret extractedFrom_eq
  boundary_append_of)
open OracleComp OracleSpec
open scoped ENNReal

attribute [local irreducible] instFintypeDigest instFintypeKState

/-! ## `roots_sound` with the seedings read through a map -/

/-- **`roots_sound`, the seeded statements read through `g`**: statements `x : X` seeded by `σ`,
whose roots are those of `g x` in a family `X'` with prefix-free roots (`hR`), where the
certificate lives. -/
theorem roots_sound_map {X X' : Type} {P : Prog Bool} {root : X' → List Ev} (g : X → X')
    (Lx : X' → Stacking) (Rx : X' → ℕ) (cl : X' → List Claim)
    (hR : RootsOK P root fun x ↦ variantProg (Lx x) (Rx x) (cl x))
    (σ : Seeds X) (hσ : ∀ x, σ.root x = root (g x))
    (hw : ∀ x, Whir.Admissible (Lx x).logN (Rx x))
    (hJ : ∀ x, (cl x).length + (Lx x).extra.length ≤ 2 ^ 46 + 1)
    (ε : ℝ≥0∞)
    (hε : ∀ x config, Whir.ladder (Lx x).logN (Rx x) = some config →
      whirEps (LeanVM.Protocol.Whir.Params.deployedCodes (Lx x).logN (Rx x)) config ≤ ε)
    (hB : ∀ x, ∀ J ≤ 2 ^ 46 + 1, eBatch J (code₀ (Lx x).logN (Rx x)) ≤ ε)
    (A : OracleComp KeccakCalls (X × Proof)) (QA : ℕ) (hA : IsTotalQueryBound A QA)
    (QV : ℕ) (hV : ∀ z, IsTotalQueryBound (verifierFam σ P z) QV) :
    Pr{let z ← romExperiment A (verifierFam σ P)}[
        z.1.2 = true ∧ RootsDoomed (fun x ↦ Lx (g x)) (fun x ↦ Rx (g x)) (fun x ↦ cl (g x)) z.1.1 z.2] ≤
      (QA + QV : ℕ) * (ε + failBound σ (QA + QV)) := by
  refine romSound_of_imp P
    (hR.cert fun x ↦ variantCertE (Lx x) (Rx x) (hw x) (cl x) (hJ x) (hε x) (hB x)) σ
    (fun x ↦ by rw [hσ]; exact hR.ok (g x)) ε
    (hR.cert_bound _ fun x h ↦ variantCertE_bound (Lx x) (Rx x) (hw x) (cl x) (hJ x) (hε x)
      (hB x) h)
    A QA hA QV hV _ fun z c hv hbad ↦ ?_
  have hnode : nodeAt P (σ.root z.1) = variantProg (Lx (g z.1)) (Rx (g z.1)) (cl (g z.1)) := by
    rw [hσ, nodeAt, hR.after]
    rfl
  rw [hnode] at hv
  obtain ⟨e, rest, hhist, hce⟩ :=
    extracted_root (L := Lx (g z.1)) (R := Rx (g z.1)) (claims := cl (g z.1)) hv
  obtain ⟨r, rest', hr, hhist'⟩ := extracted_root_word (hw (g z.1)) hv
  have he : e = Ev.commit (rootHeight (Lx (g z.1)).logN (Rx (g z.1))) (2 ^ laneFold)
      (extract (fun x ↦ c (.inl x)) r (rootHeight (Lx (g z.1)).logN (Rx (g z.1))) (2 ^ laneFold)) :=
    (List.cons.inj (hhist.symm.trans hhist')).1
  have hws := (Sound.after_extractedHistory _ _ hv).2
  rw [hhist] at hws
  unfold Doomed
  rw [hnode, hσ]
  refine ⟨root (g z.1) ++ [e], ?_, by rw [List.length_append]; omega, ?_, ?_⟩
  · rw [extractedFrom_eq _ _ _ _ _ _ hv, hhist]
    exact (List.prefix_append_right_inj _).mpr ⟨rest, rfl⟩
  · obtain ⟨level, rest', W, -, he⟩ := commitStack_after_ret hce
    rw [List.singleton_inj.1 he]
    exact boundary_append_of (h := []) trivial
  · refine (hR.D_iff _ (g z.1) [e]).2 (variantCertE_D_root (Lx (g z.1)) (Rx (g z.1)) (hw (g z.1))
      (cl (g z.1)) (hJ (g z.1)) (hε (g z.1)) (hB (g z.1)) hce
      ⟨shapeOK_root (Lx (g z.1)) (Rx (g z.1)) (hw (g z.1)) hce
        fun ht w W he ↦ hws ht w W (he ▸ List.mem_cons_self ..), fun q hq ↦ ?_⟩)
    have hq' : q ∈ Candidates (Lx (g z.1)).logN (Rx (g z.1)) (code₀ (Lx (g z.1)).logN (Rx (g z.1))).thr
        (extract (fun x ↦ c (.inl x)) r (rootHeight (Lx (g z.1)).logN (Rx (g z.1))) (2 ^ laneFold)) := by
      rw [he] at hq
      simpa [LeanVM.Protocol.Whir.Sound.wordOf, commits] using hq
    obtain ⟨cl', hcl, hn⟩ := hbad r hr q hq'
    exact ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨cl', hcl, rfl⟩), hn⟩

/-! ## The sizes -/

/-- **A size of version 1 at the per-group bound `ε`**: `15 ≤ n ≤ 28`, the deployed codes meet `ε`
above the batching lead, and the opening's query count `QO`. -/
structure PcsShape (ε : ℝ≥0∞) where
  n : ℕ
  lo : minVars ≤ n
  hi : n ≤ maxVars
  hε : ∀ config, Whir.ladder n logInvRate = some config →
    whirEps (LeanVM.Protocol.Whir.Params.deployedCodes n logInvRate) config ≤ ε
  hB : ∀ J ≤ 2 ^ 46 + 1, eBatch J (code₀ n logInvRate) ≤ ε
  QO : ℕ
  queries : ∀ (zOf : Digest → Vector E n) (w : Claim1 n × Proof),
    IsTotalQueryBound (verifierFam (seeds zOf) (famProgram (stacking n) logInvRate) w) QO

/-- **Sizes, distinct**, bundled. -/
structure PcsShapes (ε : ℝ≥0∞) where
  shs : List (PcsShape ε)
  nodup : (shs.map (·.n)).Nodup

section Union

variable {ε : ℝ≥0∞} (U : PcsShapes ε) (zOf : (n : ℕ) → Digest → Vector E n)

/-- **The union's statements**: a size's index and a claim of that size. -/
abbrev PSt : Type := Σ j : Fin U.shs.length, Claim1 (U.shs.get j).n

/-- **The certificate's statements**: a size's index and claims on its stacking. -/
abbrev PUSt : Type := Σ j : Fin U.shs.length, Stmt (stacking (U.shs.get j).n)

/-- **The union's verifier**: the indexed size's `verify_claim`. -/
def pUVer (w : PSt U × Proof) : OracleComp KeccakCalls Bool :=
  pcsVerifier (zOf (U.shs.get w.1.1).n) (w.1.2, w.2)

/-- **The union's event**: the indexed size's (`PcsDoomed`). -/
def PUDoomed (w : PSt U × Proof) (c : KeccakCalls.QueryCache) : Prop :=
  PcsDoomed (zOf (U.shs.get w.1.1).n) (w.1.2, w.2) c

/-- **The program of every size**: the index, read in unary, then the indexed size's program. -/
def pUProg : Prog Bool :=
  selProg (fun s : PcsShape ε ↦ famProgram (stacking s.n) logInvRate) U.shs

/-- **A claims' statement's root**: the reads of its index, then of its claims. -/
def pURoot (x : PUSt U) : List Ev := (selScalars x.1.1 ++ famScalars x.2).map Ev.read

theorem pURoot_eq (x : PUSt U) : pURoot U x = (selScalars x.1.1).map Ev.read ++ famHistory x.2 := by
  simp only [pURoot, List.map_append, famHistory]

/-- A claim's statement: its two claims on its stacking. -/
def pUStmt (x : PSt U) : PUSt U := ⟨x.1, toStmt (zOf (U.shs.get x.1).n x.2.root) x.2⟩

theorem after_pURoot (x : PUSt U) :
    (pUProg U).after (pURoot U x) =
      some (variantProg (stacking (U.shs.get x.1).n) logInvRate x.2.claims) := by
  rw [pURoot_eq, pUProg,
    after_selProg (fun s : PcsShape ε ↦ famProgram (stacking s.n) logInvRate) U.shs x.1.1 x.1.2]
  exact after_famHistory x.2

theorem rootOk_pURoot (x : PUSt U) : RootOk (pUProg U) (pURoot U x) := by
  have ha := after_pURoot U x
  exact ⟨reachable_of_after_reads _ ha, boundary_map_read (by simp [selScalars]),
    grindBits_map_read _, commits_map_read _, by simp [ha]⟩

theorem pURoot_inj {x x' : PUSt U} {h : List Ev} (hx : pURoot U x <+: h) (hx' : pURoot U x' <+: h) :
    x = x' := by
  obtain ⟨j, a⟩ := x
  obtain ⟨j', a'⟩ := x'
  rw [pURoot_eq] at hx hx'
  have hj : j = j' := Fin.ext (sel_eq_of_prefix j.1 j'.1 hx hx')
  subst hj
  obtain rfl : a = a' := fam_eq_of_prefix (prefix_drop_of_append hx) (prefix_drop_of_append hx')
  rfl

theorem pURootsOK :
    RootsOK (pUProg U) (pURoot U)
      fun x ↦ variantProg (stacking (U.shs.get x.1).n) logInvRate x.2.claims :=
  ⟨after_pURoot U, rootOk_pURoot U, fun hx hx' ↦ pURoot_inj U hx hx'⟩

/-- The second byte of a claim is its `n`. -/
theorem claimBytes_getD_one {n : ℕ} (x : Claim1 n) : (claimBytes x).getD 1 0 = n.toUInt8 := rfl

/-- Equal claims' bytes at sizes below `256` are of one size. -/
theorem n_eq_of_claimBytes {n n' : ℕ} {x : Claim1 n} {x' : Claim1 n'}
    (h : claimBytes x = claimBytes x') (hn : n < 256) (hn' : n' < 256) : n = n' := by
  have h1 := congrArg (fun l ↦ l.getD 1 0) h
  simp only [claimBytes_getD_one] at h1
  have h2 := congrArg UInt8.toNat h1
  simp only [Nat.toUInt8, UInt8.toNat_ofNat'] at h2
  rwa [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hn'] at h2

theorem n_lt_256 (s : PcsShape ε) : s.n < 256 := lt_of_le_of_lt s.hi (by decide)

/-- **The seedings of the union**: each claim's own (`seed1`), its root history its claims' statement's. -/
def pUSeeds : Seeds (PSt U) where
  seed x := seed1 x.2
  root x := pURoot U (pUStmt U zOf x)
  offs := []
  refs x ds hds i hi := by
    have hl : (seed1 x.2).hs.length = 1 := rfl
    rw [hl] at hds
    have hd0 : ds.getD 0 default = ds[0] := by simp [List.getD_eq_getElem?_getD, hds]
    rw [hds] at hi
    interval_cases i
    left
    show laneDigest (seedInput (ds.getD 0 default) default) = ds[0]
    rw [laneDigest_seedInput, hd0]
  cap0 x ds := capOf_seedInput _ _
  inj H hH x x' ds ds' ha ha' he := by
    obtain ⟨j, a⟩ := x
    obtain ⟨j', a'⟩ := x'
    have hl : ds.length = 1 := ha.1
    have hl' : ds'.length = 1 := ha'.1
    have hiv : ds.getD 0 default = ds'.getD 0 default := by
      have := congrArg laneDigest he
      simpa [seed1, laneDigest_seedInput] using this
    obtain ⟨f0, hf0, hH0⟩ := ha.2 0 (by omega)
    obtain ⟨f0', hf0', hH0'⟩ := ha'.2 0 (by omega)
    simp only [seed1, List.getElem?_cons_zero, Option.some.injEq] at hf0 hf0'
    subst hf0 hf0'
    have e0 : ds[0] = ds'[0] := by
      simpa [List.getD_eq_getElem?_getD, hl, hl'] using hiv
    rw [e0] at hH0
    have hb : claimBytes a = claimBytes a' := hH _ _ _ hH0 hH0'
    have hn := n_eq_of_claimBytes hb (n_lt_256 _) (n_lt_256 _)
    have hj : j = j' := by
      have hlen : j.1 < (U.shs.map (·.n)).length := by simp
      have hlen' : j'.1 < (U.shs.map (·.n)).length := by simp
      exact Fin.ext ((U.nodup.getElem_inj_iff (hi := hlen) (hj := hlen')).1 (by simpa using hn))
    subst hj
    rw [claimBytes_injective hb]

theorem verifierFam_pUSeeds (z : PSt U × Proof) :
    verifierFam (pUSeeds U zOf) (pUProg U) z =
      seedComp1 z.1.2 >>= fun seed ↦ runProofWithHash callKeccak256 callKeccakF1600
        (variantProg (stacking (U.shs.get z.1.1).n) logInvRate
          (claimsOf (zOf (U.shs.get z.1.1).n z.1.2.root) z.1.2)) seed z.2 := by
  show verifierComp _ (nodeAt (pUProg U) (pURoot U (pUStmt U zOf z.1))) z.2 = _
  rw [nodeAt, after_pURoot]
  simp only [verifierComp, LeanVM.Protocol.Compile.Rom.verify, Seed.run, Seed.hsRun, seed1,
    seedComp1, bind_assoc, pure_bind, List.nil_append, List.getD_cons_zero]
  rfl

/-- The union's program makes at most `QV` queries, above every size's `QO`. -/
theorem pUqueries (QV : ℕ) (hQV : ∀ s ∈ U.shs, s.QO ≤ QV) (z : PSt U × Proof) :
    IsTotalQueryBound (verifierFam (pUSeeds U zOf) (pUProg U) z) QV := by
  have h := (U.shs.get z.1.1).queries (zOf (U.shs.get z.1.1).n) (z.1.2, z.2)
  rw [verifierFam_seeds_eq] at h
  rw [verifierFam_pUSeeds]
  exact h.mono (hQV _ (by simp))

/-- **Fiat-Shamir soundness of PCS openings of several sizes, charged once**: an adversary of at most
`QA` queries to Keccak-256 and Keccak-f[1600] that outputs a size's index, a claim of that size and a
proof makes `verify_claim` accept while every candidate of the word extracted for the claim's root
violates `f(z) = ood` or `f(point) = value` (`z = zOf n root`) with probability at most
`(QA + QV) · (ε + 5 (QA + QV) / 2^256)`, `QV` above every size's query count. -/
theorem pcs_union_sound (A : OracleComp KeccakCalls (PSt U × Proof)) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) (QV : ℕ) (hQV : ∀ s ∈ U.shs, s.QO ≤ QV) :
    Pr{let z ← romExperiment A (pUVer U zOf)}[z.1.2 = true ∧ PUDoomed U zOf z.1.1 z.2] ≤
      ((QA + QV : ℕ) : ℝ≥0∞) * (ε + ((5 * (QA + QV) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
  have hfam := roots_sound_map (pUStmt U zOf) (fun x : PUSt U ↦ stacking (U.shs.get x.1).n)
    (fun _ ↦ logInvRate) (fun x : PUSt U ↦ x.2.claims) (pURootsOK U) (pUSeeds U zOf) (fun _ ↦ rfl)
    (fun x ↦ admissible_v1 _ (U.shs.get x.1).lo (U.shs.get x.1).hi) (fun x ↦ by
      have := x.2.short
      simp only [stacking, List.length_nil, Nat.add_zero]
      omega) ε (fun x ↦ (U.shs.get x.1).hε) (fun x ↦ (U.shs.get x.1).hB) A QA hA QV (pUqueries U zOf QV hQV)
  have hbound : ((QA + QV : ℕ) : ℝ≥0∞) * (ε + failBound (pUSeeds U zOf) (QA + QV)) =
      ((QA + QV : ℕ) : ℝ≥0∞) * (ε + ((5 * (QA + QV) : ℕ) : ℝ≥0∞) / 2 ^ 256) := by
    rw [failBound]
    simp [pUSeeds]
  rw [hbound] at hfam
  refine le_trans ?_ hfam
  have hV : verifierFam (pUSeeds U zOf) (pUProg U) = fun w ↦ seedComp1 w.1.2 >>= fun seed ↦
      runProofWithHash callKeccak256 callKeccakF1600
        (variantProg (stacking (U.shs.get w.1.1).n) logInvRate
          (claimsOf (zOf (U.shs.get w.1.1).n w.1.2.root) w.1.2)) seed w.2 :=
    funext fun w ↦ verifierFam_pUSeeds U zOf w
  have hO : pUVer U zOf = fun w ↦ if minVars ≤ (U.shs.get w.1.1).n ∧ (U.shs.get w.1.1).n ≤ maxVars then
      (seedComp1 w.1.2 >>= fun seed ↦
        if rootOf w.2 = some w.1.2.root then
          runProofWithHash callKeccak256 callKeccakF1600
            (variantProg (stacking (U.shs.get w.1.1).n) logInvRate
              (claimsOf (zOf (U.shs.get w.1.1).n w.1.2.root) w.1.2)) seed w.2
        else pure false) else pure false :=
    funext fun w ↦ pcsVerifier_eq (zOf (U.shs.get w.1.1).n) (w.1.2, w.2)
  rw [hV, hO]
  refine romExperiment_le_of_reject A (fun w ↦ seedComp1 w.1.2)
    (fun w seed ↦ runProofWithHash callKeccak256 callKeccakF1600
      (variantProg (stacking (U.shs.get w.1.1).n) logInvRate
        (claimsOf (zOf (U.shs.get w.1.1).n w.1.2.root) w.1.2)) seed w.2)
    (fun w ↦ minVars ≤ (U.shs.get w.1.1).n ∧ (U.shs.get w.1.1).n ≤ maxVars)
    (fun w ↦ rootOf w.2 = some w.1.2.root)
    (fun w cache ↦ PUDoomed U zOf w cache)
    (fun w cache ↦ RootsDoomed (fun x ↦ stacking (U.shs.get (pUStmt U zOf x).1).n) (fun _ ↦ logInvRate)
      (fun x ↦ (pUStmt U zOf x).2.claims) w cache) fun w cache _ hr hbad ↦ ?_
  intro r hr' q hq
  rw [hr'] at hr
  obtain rfl := (Option.some.inj hr).symm
  rcases hbad q hq with hne | hne
  · exact ⟨⟨(zOf _ w.1.2.root).toList, w.1.2.ood⟩, List.mem_cons_self ..,
      fun h ↦ hne ((holds_iff q ⟨(zOf _ w.1.2.root).toList, w.1.2.ood⟩).1 h)⟩
  · exact ⟨⟨w.1.2.point, w.1.2.value⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      fun h ↦ hne ((holds_iff q ⟨w.1.2.point, w.1.2.value⟩).1 h)⟩

end Union

end WhirBridge.Pcs

/-- info: 'WhirBridge.Pcs.pcs_union_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms WhirBridge.Pcs.pcs_union_sound
