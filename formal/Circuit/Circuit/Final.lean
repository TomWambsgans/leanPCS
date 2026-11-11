/-
Part of this repository. MIT OR Apache-2.0; see AGENTS.md.
-/
import Circuit.Membership

/-!
# The closed circuit `membership`

What the soundness argument needs of `membership` (`quotient::circuit::membership`), on row numbers:

* `membership_rows_size`: `2^22` rows (the rows used fit: `buildRows = 4,002,624`);
* `membership_input_row`: an input row reads its own output in `X`, `Y`, `C`;
* `membership_random_row`: the last `16` rows (`IsRandom`, past the `3,878,612` rows built:
  `membership_usedRows_le`) are random rows, `X` reading the row's own output, `Y` one, `C` zero;
* `membership_order`: every other row reads constants or rows of lower `rank` (`rank r = r` from
  row `512` on, `2^22 + r` for the public rows `r < 512`, ranked last), and
  `membership_reads_used`: built rows (`ReadsUsed`), so never a random row;
* `membership_word5`, `membership_word4_one`, `membership_word4`: the anchors of the constants;
* `membership_public`: for every valuation satisfying every row's gate whose input bits are a
  well-formed secret's, bit `j` of public word `J < 4` is bit `j % 8` of byte `15 - j / 8` of the
  half `J % 2` of `y` (`J < 2`) or of the root (`statement::halves`, big-endian);
* `secretInputs_ofBits`: any input bits are those of the secret `secretOfBits` reads off them.

Nothing here evaluates the circuit: `membership` is reached through `spec_membershipBuild` and
the definition of `finish`, the rows' builder kept abstract.
-/

set_option maxRecDepth 10000

namespace PcsCircuit

open Builder

/-- `membership` is `finish` of the run of `membershipBuild`. -/
theorem membership_eq : membership = (runBuild membershipBuild Builder.new).2.finish logRows
    (publicWords (runBuild membershipBuild Builder.new).1.1 (runBuild membershipBuild Builder.new).1.2) := rfl

attribute [local irreducible] runB IsRow Below Valid

/-- The rank of a row: its number, the public rows ranked last. -/
def rank (r : Nat) : Nat := if r < publicRows then 2 ^ logRows + r else r

/-- A source a row of rank `rk` may read: a constant, or a row of the circuit of lower rank. -/
def Ranked (rk : Nat) : Src → Prop
  | .row r' => r' < 2 ^ logRows ∧ rank r' < rk
  | _ => True

/-- What the cell of bit `j` of public word `J` reads: the `X` (even `j`) or `Y` (odd `j`) cell of
row `64 J + j / 2`. -/
def pubSrcN (c : Circuit) (J j : Nat) : Src :=
  if j % 2 = 0 then (c.rows.getD (64 * J + j / 2) .idle).x else (c.rows.getD (64 * J + j / 2) .idle).y

theorem finish_rows_size (b : Builder) (pub : Nat → Nat → Src) :
    (b.finish logRows pub).rows.size = 2 ^ logRows := by
  simp [Builder.finish, Builder.finishRows]

theorem finish_rows_getD (b : Builder) (pub : Nat → Nat → Src) (r : Nat) (hr : r < 2 ^ logRows) :
    (b.finish logRows pub).rows.getD r .idle =
      if r < publicRows then publicRow pub r
      else if b.rows.size ≤ r ∧ 2 ^ logRows - randomRows ≤ r then randomRow r
      else b.rows.getD r .idle := by
  simp only [Builder.finish, Builder.finishRows]
  rw [map_range_getD _ _ _ _ hr]

theorem finish_inputs (b : Builder) (pub : Nat → Nat → Src) : (b.finish logRows pub).inputs = b.inputs := rfl

theorem finish_usedRows (b : Builder) (pub : Nat → Nat → Src) :
    (b.finish logRows pub).usedRows = b.rows.size := rfl

/-- A row of `b` below its size is not a random row of `finish`. -/
theorem finish_rows_getD_built (b : Builder) (pub : Nat → Nat → Src) (r : Nat) (hr : r < 2 ^ logRows)
    (hp : publicRows ≤ r) (hb : r < b.rows.size) : (b.finish logRows pub).rows.getD r .idle = b.rows.getD r .idle := by
  rw [finish_rows_getD _ _ _ hr, if_neg (by omega), if_neg (by omega)]

/-- `membership` is `finish` of the membership rows. -/
theorem membership_spec :
    ∃ y root bf, membership = bf.finish logRows (publicWords y root) ∧
    WF bf ∧ bf.rows.size ≤ buildRows ∧ bf.inputs.size = 256 + 257 * depth ∧
    (∀ k < 256, Valid bf (y.getD k .zero) ∧ Valid bf (root.getD k .zero)) ∧
    ∀ s : Secret, s.WellFormed → ∀ v, Sat v bf → SecretInputs s v bf.inputs →
      ∀ k < 256, read v (y.getD k .zero) = bitOf s.y k ∧ read v (root.getD k .zero) = bitOf s.root k := by
  obtain ⟨y, root, bf, heq, h⟩ := spec_membershipBuild
  rw [runB_eq] at heq
  exact ⟨y, root, bf, by rw [membership_eq, heq], h⟩

/-- **`2^22` rows.** -/
theorem membership_rows_size : membership.rows.size = 2 ^ logRows := by
  obtain ⟨y, root, bf, he, -⟩ := membership_spec
  rw [he, finish_rows_size]

theorem publicWords_valid {y root : Array Src} {bf : Builder}
    (h : ∀ k < 256, Valid bf (y.getD k .zero) ∧ Valid bf (root.getD k .zero)) (J j : Nat) (hj : j < 128) :
    Valid bf (publicWords y root J j) := by
  unfold publicWords
  have hk : 8 * (16 * (J % 2) + 15 - j / 8) + j % 8 < 256 := by
    have : J % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  split
  · exact (h _ hk).1
  · exact (h _ hk).2

theorem valid_ranked {bf : Builder} {s : Src} (hs : Valid bf s) (hb : bf.rows.size ≤ 2 ^ logRows) (rk : Nat)
    (hrk : 2 ^ logRows ≤ rk) : Ranked rk s := by
  unfold Valid at hs
  cases s with
  | zero => trivial
  | one => trivial
  | row r' =>
    unfold Below at hs
    refine ⟨by omega, ?_⟩
    unfold rank; rw [if_neg (by omega)]; omega

theorem below_ranked {r : Nat} {s : Src} (hs : Below r s) (hr : r < 2 ^ logRows) (hr' : publicRows ≤ r) :
    Ranked (rank r) s := by
  cases s with
  | zero => trivial
  | one => trivial
  | row r' =>
    unfold Below at hs
    refine ⟨by omega, ?_⟩
    unfold rank; rw [if_neg (by omega), if_neg (by omega)]; omega

theorem buildRows_lt : buildRows ≤ 2 ^ logRows := by rw [buildRows_eq]; decide

/-- **An input row reads its own output** in `X`, `Y`, `C`. -/
theorem membership_input_row : ∀ r ∈ membership.inputs, r < 2 ^ logRows ∧ publicRows ≤ r ∧
    membership.rows.getD r .idle = ⟨.row r, .row r, .row r⟩ := by
  obtain ⟨y, root, bf, he, hwf, hsize, -⟩ := membership_spec
  intro r hr
  rw [he, finish_inputs] at hr
  have h1 := hwf.input_range r hr
  have hlt : r < 2 ^ logRows := by have := buildRows_lt; omega
  refine ⟨hlt, h1.1, ?_⟩
  rw [he, finish_rows_getD_built _ _ _ hlt h1.1 h1.2]
  exact hwf.input_row r hr

/-- Row `r` of `membership` is a random row (`finish`): one of the last `16`, not built. -/
def IsRandom (r : Nat) : Prop := IsRandomRow logRows membership.usedRows r

/-- **The rows built leave room for the random rows**: `3,878,612 ≤ buildRows = 4,002,624 ≤ 2^22 − 16`. -/
theorem membership_usedRows_le : membership.usedRows ≤ 2 ^ logRows - randomRows := by
  obtain ⟨y, root, bf, he, -, hsize, -⟩ := membership_spec
  rw [he, finish_usedRows]
  have := buildRows_eq
  simp only [logRows, randomRows, Nat.reducePow, Nat.reduceSub] at this ⊢
  omega

/-- **A random row reads its own output in `X`, the one in `Y`, the zero in `C`.** -/
theorem membership_random_row (r : Nat) (h : IsRandom r) :
    membership.rows.getD r .idle = randomRow r := by
  obtain ⟨y, root, bf, he, -⟩ := membership_spec
  obtain ⟨h1, h2, h3⟩ := h
  rw [he, finish_usedRows] at h1
  have hp : ¬ r < publicRows := by
    simp only [publicRows, logRows, randomRows, Nat.reducePow, Nat.reduceSub] at h2 ⊢
    omega
  rw [he, finish_rows_getD _ _ _ h3, if_neg hp, if_pos ⟨h1, h2⟩]

/-- **The random rows are not inputs.** -/
theorem membership_random_not_input (r : Nat) (h : IsRandom r) : r ∉ membership.inputs := by
  intro hin
  have h1 := (membership_input_row r hin).2.2
  rw [membership_random_row r h] at h1
  cases h1

/-- **Every other row reads constants or rows of lower rank**, the public rows ranked last. -/
theorem membership_order : ∀ r < 2 ^ logRows, r ∉ membership.inputs → ¬ IsRandom r →
    Ranked (rank r) (membership.rows.getD r .idle).x ∧ Ranked (rank r) (membership.rows.getD r .idle).y ∧
    Ranked (rank r) (membership.rows.getD r .idle).c := by
  obtain ⟨y, root, bf, he, hwf, hsize, -, hval, -⟩ := membership_spec
  have hb : bf.rows.size ≤ 2 ^ logRows := le_trans hsize buildRows_lt
  intro r hr hin hrand
  rw [he, finish_inputs] at hin
  unfold IsRandom IsRandomRow at hrand
  rw [he, finish_usedRows] at hrand
  rw [he, finish_rows_getD _ _ _ hr]
  by_cases hp : r < publicRows
  · rw [if_pos hp]
    have hrk : 2 ^ logRows ≤ rank r := by unfold rank; rw [if_pos hp]; omega
    have pb : ∀ J j, j < 128 → Ranked (rank r) (publicBit (publicWords y root) J j) := by
      intro J j hj
      unfold publicBit
      split
      · exact valid_ranked (publicWords_valid hval J j hj) hb _ hrk
      · split <;> trivial
    unfold publicRow
    exact ⟨pb _ _ (by omega), pb _ _ (by omega), trivial⟩
  · rw [if_neg hp, if_neg (fun h => hrand ⟨h.1, h.2, hr⟩)]
    by_cases hu : r < bf.rows.size
    · obtain ⟨h1, h2, h3⟩ := hwf.order r (by omega) hu hin
      exact ⟨below_ranked h1 hr (by omega), below_ranked h2 hr (by omega), below_ranked h3 hr (by omega)⟩
    · have : bf.rows.getD r .idle = Row.idle := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl
      rw [this]
      exact ⟨trivial, trivial, trivial⟩

/-- A source reading a row built, of the first `u`. -/
def ReadsUsed (u : Nat) : Src → Prop
  | .row r' => r' < u
  | _ => True

theorem valid_readsUsed {bf : Builder} {s : Src} (hs : Valid bf s) : ReadsUsed bf.rows.size s := by
  unfold Valid at hs
  cases s with
  | zero => trivial
  | one => trivial
  | row r' => unfold Below at hs; exact hs.2

theorem below_readsUsed {u r : Nat} {s : Src} (hs : Below r s) (hr : r < u) : ReadsUsed u s := by
  cases s with
  | zero => trivial
  | one => trivial
  | row r' => unfold Below at hs; show r' < u; omega

/-- **The rows other than inputs and random rows read built rows**, so never a random row. -/
theorem membership_reads_used : ∀ r < 2 ^ logRows, r ∉ membership.inputs → ¬ IsRandom r →
    ReadsUsed membership.usedRows (membership.rows.getD r .idle).x ∧
    ReadsUsed membership.usedRows (membership.rows.getD r .idle).y ∧
    ReadsUsed membership.usedRows (membership.rows.getD r .idle).c := by
  obtain ⟨y, root, bf, he, hwf, hsize, -, hval, -⟩ := membership_spec
  intro r hr hin hrand
  rw [he, finish_inputs] at hin
  unfold IsRandom IsRandomRow at hrand
  rw [he, finish_usedRows] at hrand ⊢
  rw [finish_rows_getD _ _ _ hr]
  by_cases hp : r < publicRows
  · rw [if_pos hp]
    have pb : ∀ J j, j < 128 → ReadsUsed bf.rows.size (publicBit (publicWords y root) J j) := by
      intro J j hj
      unfold publicBit
      split
      · exact valid_readsUsed (publicWords_valid hval J j hj)
      · split <;> trivial
    unfold publicRow
    exact ⟨pb _ _ (by omega), pb _ _ (by omega), trivial⟩
  · rw [if_neg hp, if_neg (fun h => hrand ⟨h.1, h.2, hr⟩)]
    by_cases hu : r < bf.rows.size
    · obtain ⟨h1, h2, h3⟩ := hwf.order r (by omega) hu hin
      exact ⟨below_readsUsed h1 hu, below_readsUsed h2 hu, below_readsUsed h3 hu⟩
    · have : bf.rows.getD r .idle = Row.idle := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl
      rw [this]
      exact ⟨trivial, trivial, trivial⟩

theorem pubSrcN_finish (bf : Builder) (pub : Nat → Nat → Src) (J j : Nat) (hJ : J < 8) (hj : j < 128) :
    pubSrcN (bf.finish logRows pub) J j = publicBit pub J j := by
  unfold pubSrcN
  rw [finish_rows_getD _ _ _ (by unfold logRows; omega),
    if_pos (show 64 * J + j / 2 < publicRows by unfold publicRows; omega)]
  have e1 : (64 * J + j / 2) / 64 = J := by omega
  have e2 : (64 * J + j / 2) % 64 = j / 2 := by omega
  simp only [publicRow, e1, e2]
  by_cases h : j % 2 = 0
  · rw [if_pos h, show 2 * (j / 2) = j by omega]
  · rw [if_neg h, show 2 * (j / 2) + 1 = j by omega]

/-- **Word 5 reads the zero.** -/
theorem membership_word5 (j : Nat) (hj : j < 128) : pubSrcN membership 5 j = .zero := by
  obtain ⟨y, root, bf, he, -⟩ := membership_spec
  rw [he, pubSrcN_finish _ _ _ _ (by decide) hj]; unfold publicBit; simp

/-- **Words 5 to 7 read the zero.** -/
theorem membership_high (J j : Nat) (hJ5 : 5 ≤ J) (hJ : J < 8) (hj : j < 128) : pubSrcN membership J j = .zero := by
  obtain ⟨y, root, bf, he, -⟩ := membership_spec
  rw [he, pubSrcN_finish _ _ _ _ hJ hj]; unfold publicBit
  rw [if_neg (by omega), if_neg (by omega)]

/-- **Bit 0 of word 4 reads the one.** -/
theorem membership_word4_one : pubSrcN membership 4 0 = .one := by
  obtain ⟨y, root, bf, he, -⟩ := membership_spec
  rw [he, pubSrcN_finish _ _ _ _ (by decide) (by decide)]; unfold publicBit; simp

/-- **The other bits of word 4 read the zero.** -/
theorem membership_word4 (j : Nat) (hj0 : j ≠ 0) (hj : j < 128) : pubSrcN membership 4 j = .zero := by
  obtain ⟨y, root, bf, he, -⟩ := membership_spec
  rw [he, pubSrcN_finish _ _ _ _ (by decide) hj]; unfold publicBit; simp [hj0]

/-- `v` satisfies every row's gate of the closed circuit. -/
def CircuitSat (c : Circuit) (v : Nat → Bool) : Prop :=
  ∀ r < c.rows.size, v r = (c.rows.getD r .idle).eval v

/-- **The public words are the statement's bits.** For every valuation satisfying `membership`
whose input bits are those of a well-formed secret, bit `j` of public word `J < 4` is bit `j % 8`
of byte `16 (J % 2) + 15 - j / 8` of `y` (words `0`, `1`) or of the root (words `2`, `3`). -/
theorem membership_public (v : Nat → Bool) (hv : CircuitSat membership v) (s : Secret) (hs : s.WellFormed)
    (hin : SecretInputs s v membership.inputs) (J j : Nat) (hJ : J < 4) (hj : j < 128) :
    read v (pubSrcN membership J j) =
      ((if J < 2 then s.y else s.root).getD (16 * (J % 2) + 15 - j / 8) 0).toNat.testBit (j % 8) := by
  obtain ⟨y, root, bf, he, hwf, hsize, -, hval, hsem⟩ := membership_spec
  have hb : bf.rows.size ≤ 2 ^ logRows := le_trans hsize buildRows_lt
  have hsat : Sat v bf := by
    intro r h1 h2
    have := hv r (by rw [he, finish_rows_size]; omega)
    rw [he, finish_rows_getD_built _ _ _ (by omega) h1 h2] at this
    exact this
  rw [he, finish_inputs] at hin
  have hk : 8 * (16 * (J % 2) + 15 - j / 8) + j % 8 < 256 := by
    have : J % 2 < 2 := Nat.mod_lt _ (by decide)
    omega
  obtain ⟨hy, hr⟩ := hsem s hs v hsat hin _ hk
  rw [he, pubSrcN_finish _ _ _ _ (by omega) hj]
  unfold publicBit publicWords
  rw [if_pos hJ]
  have e1 : (8 * (16 * (J % 2) + 15 - j / 8) + j % 8) / 8 = 16 * (J % 2) + 15 - j / 8 := by omega
  have e2 : (8 * (16 * (J % 2) + 15 - j / 8) + j % 8) % 8 = j % 8 := by omega
  by_cases h2 : J < 2
  · rw [if_pos h2, if_pos h2, hy]; unfold bitOf; rw [e1, e2]
  · rw [if_neg h2, if_neg h2, hr]; unfold bitOf; rw [e1, e2]

/-- **Any input bits are a well-formed secret's**: the one `secretOfBits` reads off them. -/
theorem secretOfBits_wellFormed (bits : Nat → Bool) : (secretOfBits bits).WellFormed := by
  refine ⟨bytesOfBits_length _, fun i hi => ?_⟩
  simp only [secretOfBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some, bytesOfBits_length]

theorem secretInputs_ofBits (v : Nat → Bool) (ins : Array Nat) :
    SecretInputs (secretOfBits fun k => v (ins.getD k 0)) v ins := by
  refine ⟨fun k hk => (bitOf_bytesOfBits (fun k => v (ins.getD k 0)) k hk).symm, fun i hi => ⟨fun j hj => ?_, ?_⟩⟩
  · simp only [secretOfBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some]
    exact (bitOf_bytesOfBits (fun j => v (ins.getD (256 + 257 * i + j) 0)) j hj).symm
  · simp only [secretOfBits]
    rw [bitsToNat_testBit]
    simp [List.getD_eq_getElem?_getD, hi]

end PcsCircuit
