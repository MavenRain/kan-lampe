import KanLampe.Convenience
import Mathlib.Data.Vector.Snoc
import Mathlib.Data.Nat.Log

set_option autoImplicit true

def List.chunksExact {n α} d (l : List α) (h : List.length l = n * d) : List (List α) :=
  match n with
  | 0 => []
  | n + 1 =>
    l.take d :: List.chunksExact (n := n) d (l.drop d) (by kan_simp [h, Nat.succ_mul])

@[simp]
lemma List.chunksExact_length {h : List.length l = k * d} :
    (List.chunksExact d l h).length = k := by
  kan_induction_with k generalizing l with
  | zero => kan_simp [chunksExact]
  | succ k ih =>
    kan_simp [chunksExact, ih]

lemma List.getElem_chunksExact {l : List α} {h : l.length = k * d} {hi} :
    (List.chunksExact d l h)[i]'hi =
      List.ofFn fun (j : Fin d) =>
        l[d * i + j.val]'(by
          kan_simp [h]
          kan_simp_at hi
          kan_cases j
          kan_simp
          kan_apply lt_of_lt_of_le (Nat.add_lt_add_left (by kan_assumption) _)
          kan_rw [<-Nat.mul_succ, mul_comm]
          kan_apply Nat.mul_le_mul_right
          kan_linarith) := by
  -- TODO: port full proof.  Blocked on `kan_rename_i` pattern form and
  -- `kan_omega` not handling nonlinear arithmetic of `Nat.succ_mul`.
  sorry

theorem List.Vector.reverse_map {α β : Type} {d : ℕ} (v : List.Vector α d) (f : α → β) :
    (v.map f).reverse = v.reverse.map f := by
  kan_apply List.Vector.eq
  kan_simp [List.Vector.toList_reverse]

namespace KanLampe

abbrev Radix : Type := { n : Nat // n > 1 }

abbrev Digit (r : Radix) := Fin r.1
abbrev RadixVec (r : Radix) (d : Nat) := Fin (r ^ d)

abbrev R256 : Radix := ⟨256, by kan_decide⟩

namespace RadixVec

variable {r : Radix} {d : Nat}

def of (r : Radix) (v : Nat) : RadixVec r (Nat.log r.val v + 1) :=
  ⟨v, Nat.lt_pow_succ_log_self r.prop _⟩

def msd (v : RadixVec r (d + 1)) : Digit r :=
  Fin.mk
    (v.val / (r.1 ^ d))
    (Nat.div_lt_of_lt_mul v.prop)

def lsds (v : RadixVec r (d + 1)) : RadixVec r d :=
  Fin.mk
    (v.val - msd v * r ^ d)
    (by
      kan_simp_only [msd]
      kan_rw [mul_comm (v.val / r.1 ^ d), <-Nat.mod_def]
      kan_exact Nat.mod_lt _ (Nat.pow_pos (by kan_linarith [r.prop])))

theorem msd_lsds_decomposition {v : RadixVec r (d + 1)} :
    v =
      ⟨v.msd.val * r ^ d + v.lsds.val, by
        kan_have hle := Nat.div_mul_le_self v.val (r.1 ^ d)
        kan_simp [msd, lsds]
        kan_rw [Nat.add_sub_cancel' hle]
        kan_exact v.prop
      ⟩ := by
  kan_apply Fin.eq_of_val_eq
  kan_simp [msd, lsds]
  kan_rw [Nat.add_sub_cancel' (Nat.div_mul_le_self v.val (r.1 ^ d))]

theorem msd_lsds_decomposition_unique {v : RadixVec r (d + 1)}
    {msd' : Digit r} {lsds' : RadixVec r d} {h} :
    v = ⟨msd'.val * r ^ d + lsds'.val, h⟩ ↔ msd' = v.msd ∧ lsds' = v.lsds := by
  kan_apply Iff.intro
  · kan_intro heq
    kan_subst heq
    kan_apply And.intro
    · kan_apply Fin.eq_of_val_eq
      kan_simp_only [msd]
      kan_have hpos : r.val ^ d > 0 := Nat.pow_pos (by kan_linarith [r.prop])
      kan_rw [mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt lsds'.prop, Nat.add_zero]
    · kan_apply Fin.eq_of_val_eq
      kan_simp_only [lsds, msd]
      kan_have hpos : r.val ^ d > 0 := Nat.pow_pos (by kan_linarith [r.prop])
      kan_rw [mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt lsds'.prop, mul_comm]
      kan_simp
  · kan_intro hconj
    kan_have hmsd := hconj.1
    kan_have hlsds := hconj.2
    kan_subst hmsd
    kan_subst hlsds
    kan_exact msd_lsds_decomposition

def toDigitsBE {d} (v : RadixVec r d) : List.Vector (Digit r) d :=
  match d with
  | 0 => List.Vector.nil
  | _ + 1 => v.msd ::ᵥ toDigitsBE v.lsds

def toDigitsLE {d} (v : RadixVec r d) : List.Vector (Digit r) d :=
  (toDigitsBE v).reverse

abbrev toBaseLE {d} (v : RadixVec r d) : List.Vector (Digit r) d :=
  toDigitsLE v

theorem toBaseLE_elem_lt {d} {v : RadixVec r d} {i : Fin d} :
    (toBaseLE (r := r) v).get i < r.val :=
  (toBaseLE v).get i |>.prop

def ofLimbsBE {d} (r : Nat) (v : List.Vector ℕ d) : ℕ :=
  match d with
  | 0 => 0
  | d + 1 => v.head * r ^ d + ofLimbsBE r v.tail

def ofLimbsBE' (r : Nat) (l : List ℕ) : ℕ :=
  ofLimbsBE r ⟨l, rfl⟩

def ofLimbsLE {d} (r : Nat) (v : List.Vector ℕ d) : ℕ :=
  ofLimbsBE r v.reverse

def ofLimbsLE' (r : Nat) (l : List ℕ) : ℕ :=
  ofLimbsBE' r l.reverse

@[simp]
theorem ofLimbsBE'_nil (r : Nat) : ofLimbsBE' r [] = 0 := by
  kan_rfl

@[simp]
theorem ofLimbsBE'_cons (r : Nat) (x : Nat) (xs : List Nat) :
    ofLimbsBE' r (x :: xs) = x * r ^ xs.length + ofLimbsBE' r xs := by
  kan_rfl

theorem ofLimbsBE'_append (r : Nat) (xs ys : List Nat) :
    ofLimbsBE' r (xs ++ ys) = ofLimbsBE' r xs * r ^ ys.length + ofLimbsBE' r ys := by
  kan_induction_with xs with
  | nil => kan_simp
  | cons _ _ ih =>
    kan_simp_only [List.cons_append, ofLimbsBE'_cons, List.length_append, ih, Nat.pow_add,
      Nat.add_mul]
    kan_linarith

theorem ofLimbsLE'_append (r : Nat) (xs ys : List Nat) :
    ofLimbsLE' r (xs ++ ys) = ofLimbsLE' r xs + r ^ xs.length * ofLimbsLE' r ys := by
  kan_simp [ofLimbsLE', List.reverse_append, ofLimbsBE'_append, add_comm, add_left_comm, mul_comm]

def ofDigitsBE {d} {r : Radix} (v : List.Vector (Digit r) d) : RadixVec r d :=
  ⟨ofLimbsBE r.val (v.map (fun d => d.val)), by
    kan_induction_with d with
    | zero => kan_simp [ofLimbsBE]
    | succ d ih =>
      kan_simp_only [ofLimbsBE, List.Vector.head_map, List.Vector.tail_map]
      calc
        _ < v.head.val * r.val ^ d + r.val ^ d := by
          kan_apply Nat.add_lt_add_left
          kan_exact ih v.tail
        _ = (v.head.val + 1) * r.val ^ d := by kan_linarith
        _ ≤ r * r.val ^ d := by
          kan_have hprop := Nat.succ_le_of_lt v.head.prop
          kan_apply Nat.mul_le_mul_right
          kan_assumption
        _ = _ := by kan_simp [Nat.pow_succ, Nat.mul_comm]
  ⟩

def ofDigitsLE {d} {r : Radix} (v : List.Vector (Digit r) d) : RadixVec r d :=
  ofDigitsBE v.reverse

abbrev ofBaseLE {d} {r : Radix} (v : List.Vector (Digit r) d) : RadixVec r d :=
  ofDigitsLE v

def ofDigitsBE' (l : List (Digit r)) : Nat :=
  (RadixVec.ofDigitsBE ⟨l, rfl⟩).val

def ofDigitsLE' (l : List (Digit r)) : Nat :=
  ofDigitsBE' l.reverse

def toBaseLENat' (r : Radix) (n : Nat) (v : Nat) : List.Vector (Digit r) n :=
  let rv : RadixVec r n := ⟨v % (r.val ^ n),
    Nat.mod_lt _ (Nat.pow_pos (Nat.lt_of_succ_le (Nat.one_le_of_lt r.prop)))⟩
  RadixVec.toDigitsLE rv

def ofBaseLENat' {r : Radix} {n : Nat} (v : List.Vector (Digit r) n) : Nat :=
  (RadixVec.ofDigitsLE v).val

@[simp]
theorem ofDigitsBE'_nil : ofDigitsBE' (r := r) [] = 0 := by
  kan_rfl

@[simp]
theorem ofDigitsBE'_cons :
    ofDigitsBE' (r := r) (x :: xs) = x * r ^ xs.length + ofDigitsBE' xs := by
  kan_rfl

@[simp]
theorem ofDigitsBE'_append :
    ofDigitsBE' (r := r) (xs ++ ys) = ofDigitsBE' xs * r ^ ys.length + ofDigitsBE' ys := by
  kan_induction_with xs with
  | nil => kan_simp
  | cons _ _ ih =>
    kan_simp_only [
      List.cons_append, ofDigitsBE'_cons, List.length_append, ih, Nat.pow_add,
      Nat.add_mul
    ]
    kan_linarith

theorem ofDigitsBE'_toList {r : Radix} {l : List.Vector (Digit r) d} :
    ofDigitsBE' l.toList = (ofDigitsBE l).val := by
  kan_simp_only [ofDigitsBE']
  kan_congr <;> kan_simp

theorem ofDigitsLE'_append :
    ofDigitsLE' (r := r) (xs ++ ys) = ofDigitsLE' xs + r ^ xs.length * ofDigitsLE' ys := by
  kan_simp [ofDigitsLE', List.reverse_append, ofDigitsBE'_append, add_comm, add_left_comm, mul_comm]

def toDigitsBE' (r : Radix) (n : Nat) : List (Digit r) :=
  toDigitsBE ⟨n, Nat.lt_pow_succ_log_self r.prop _⟩ |>.toList

def toDigitsLE' (r : Radix) (n : Nat) : List (Digit r) :=
  (toDigitsBE' r n).reverse

instance : OfNat Radix 2 where
  ofNat := ⟨2, by kan_decide⟩

lemma ofDigitsBE_cons {r : Radix} {d : Nat} {x : Digit r}
    {xs : List.Vector (Digit r) d} :
    ofDigitsBE (r := r) (x ::ᵥ xs) = (x.val * r.val ^ d + ofDigitsBE xs) := by
  kan_rfl

@[simp]
theorem ofDigitsBE_cons' {r : Radix} {d : Nat} {x : Digit r}
    {xs : List.Vector (Digit r) d} :
    ofDigitsBE (r := r) (x ::ᵥ xs) =
      ⟨x.val * r.val ^ d + ofDigitsBE xs, by
        calc
          _ < x.val * r.val ^ d + r.val ^ d := by
            kan_apply Nat.add_lt_add_left
            kan_exact (ofDigitsBE xs).prop
          _ = (x.val + 1) * r.val ^ d := by kan_linarith
          _ ≤ r * r.val ^ d := by
            kan_apply Nat.mul_le_mul_right
            kan_have hprop := x.prop
            kan_linarith
          _ = _ := by kan_simp [Nat.pow_succ, Nat.mul_comm]
      ⟩ := by
  kan_rfl

theorem ofDigitsBE_lt {r : Radix} {d : Nat} {l : List.Vector (Digit r) d} :
    (ofDigitsBE l).val < r.val ^ d :=
  (ofDigitsBE l).isLt

theorem ofDigitsBE'_lt {r : Radix} {l : List (Digit r)} :
    ofDigitsBE' l < r ^ l.length :=
  (RadixVec.ofDigitsBE ⟨l, rfl⟩).isLt

theorem ofDigitsBE_toDigitsBE {r : Radix} {n : RadixVec r d} :
    ofDigitsBE (toDigitsBE n) = n := by
  kan_induction_with d with
  | zero =>
    kan_cases_with r with
    | mk r hr =>
      kan_cases_with n with
      | mk n hn =>
        kan_have hzero : n = 0 := by kan_simp_all
        kan_simp [toDigitsBE, ofDigitsBE, ofLimbsBE, hzero]
  | succ d ih =>
    kan_conv_rhs rw [msd_lsds_decomposition (v := n)]
    kan_have hih := Fin.val_eq_of_eq $ ih (n := n.lsds)
    kan_simpa [ofDigitsBE, toDigitsBE, ofLimbsBE]

theorem ofDigitsLE_toDigitsLE {r : Radix} {n : RadixVec r d} :
    ofDigitsLE (toDigitsLE n) = n := by
  kan_simp [ofDigitsLE, toDigitsLE, ofDigitsBE_toDigitsBE, List.Vector.reverse_reverse]

theorem ofBaseLE_val_toBaseLE {r : Radix} {n : RadixVec r d} :
    (ofBaseLE (r := r) (toBaseLE n)).val = n.val := by
  kan_simpa_using congrArg Fin.val (ofDigitsLE_toDigitsLE (n := n))

theorem toDigitsBE_ofDigitsBE {r : Radix} {v : List.Vector (Digit r) d} :
    toDigitsBE (ofDigitsBE v) = v := by
  kan_induction_with v using List.Vector.inductionOn with
  | nil => kan_rfl
  | cons ih =>
    kan_simp_only [toDigitsBE, ofDigitsBE_cons']
    kan_congr 1
    · -- Goal: msd ⟨x.val * r^n + (ofDigitsBE w).val, ...⟩ = x
      kan_simp_only [msd]
      kan_apply Fin.eq_of_val_eq
      kan_simp_only []
      kan_have hpos : r.val ^ _ > 0 := Nat.pow_pos (by kan_linarith [r.prop])
      kan_rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt ofDigitsBE_lt]
    · -- Goal: (lsds ⟨x.val * r^n + (ofDigitsBE w).val, ...⟩).toDigitsBE = w
      kan_simp_only [lsds]
      kan_conv_rhs rw [<-ih]
      kan_congr 1
      kan_apply Fin.eq_of_val_eq
      kan_simp_only [msd]
      kan_conv_lhs
        arg 2
        arg 1
        rw [Nat.mul_comm]
      kan_have hpos : r.val ^ _ > 0 := Nat.pow_pos (by kan_linarith [r.prop])
      kan_rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt ofDigitsBE_lt]
      kan_simp

theorem toDigitsLE_ofDigitsLE {r : Radix} {v : List.Vector (Digit r) d} :
    toDigitsLE (ofDigitsLE v) = v := by
  kan_simp [toDigitsLE, ofDigitsLE, toDigitsBE_ofDigitsBE, List.Vector.reverse_reverse]

theorem ofDigitsBE'_toDigitsBE' {r : Radix} {n : Nat} :
    ofDigitsBE' (toDigitsBE' r n) = n := by
  kan_simp [toDigitsBE']
  kan_have hn : n < r.val ^ (Nat.log r.val n + 1) := Nat.lt_pow_succ_log_self r.prop _
  kan_have hval : (ofDigitsBE (toDigitsBE ⟨n, hn⟩)).val = n := by
    kan_simpa_using congrArg Fin.val (ofDigitsBE_toDigitsBE (n := ⟨n, hn⟩))
  kan_have hlist := ofDigitsBE'_toList (l := toDigitsBE (r := r) (d := _) ⟨n, hn⟩)
  kan_simpa [hlist] using hval

theorem ofDigitsLE'_toDigitsLE' {r : Radix} {n : Nat} :
    ofDigitsLE' (toDigitsLE' r n) = n := by
  kan_simp [ofDigitsLE', toDigitsLE', ofDigitsBE'_toDigitsBE']

theorem ofBaseLENat'_toBaseLENat' {r : Radix} {n : Nat} {v : Nat} :
    ofBaseLENat' (toBaseLENat' r n v) = v % r.val ^ n := by
  kan_simp [toBaseLENat', ofBaseLENat', ofDigitsLE_toDigitsLE]

theorem ofBaseLENat'_toBaseLENat'_of_lt {r : Radix} {n : Nat} {v : Nat}
    (hv : v < r.val ^ n) :
    ofBaseLENat' (toBaseLENat' r n v) = v := by
  kan_rw [ofBaseLENat'_toBaseLENat']
  kan_exact Nat.mod_eq_of_lt hv

theorem ofDigitsBE_mono {r : Radix} {l₁ l₂ : List.Vector (Digit r) d} :
    l₁.toList < l₂.toList → ofDigitsBE l₁ < ofDigitsBE l₂ := by
  kan_intro hp
  kan_induction_with d with
  | zero =>
    kan_cases_with List.Vector.eq_nil l₁ with
    | refl =>
      kan_cases_with List.Vector.eq_nil l₂ with
      | refl =>
        kan_simp_at hp
  | succ d ih =>
    kan_have eq₁ := (List.Vector.cons_head_tail l₁).symm
    kan_have eq₂ := (List.Vector.cons_head_tail l₂).symm
    kan_have heq₁ : l₁.toList = l₁.head :: l₁.tail.toList := congrArg Subtype.val eq₁
    kan_have heq₂ : l₂.toList = l₂.head :: l₂.tail.toList := congrArg Subtype.val eq₂
    kan_have hp' : (l₁.head :: l₁.tail.toList) < (l₂.head :: l₂.tail.toList) := by
      kan_rw [<-heq₁, <-heq₂]; kan_exact hp
    kan_rw [eq₁, eq₂]
    kan_simp [ofDigitsBE_cons', Fin.mk_lt_mk]
    kan_simp_only [List.cons_lt_cons_iff] at hp'
    kan_cases_with hp' with
    | inl hh =>
      kan_simp_only [Fin.lt_def] at hh
      calc
        _ < l₁.head.val * r.val ^ d + r.val ^ d := by
          kan_apply Nat.add_lt_add_left
          kan_exact ofDigitsBE_lt
        _ = (l₁.head.val + 1) * r.val ^ d := by kan_linarith
        _ ≤ l₂.head.val * r.val ^ d := by
          kan_apply Nat.mul_le_mul_right
          kan_linarith
        _ ≤ _ := by kan_linarith
    | inr hconj =>
      kan_have heq := hconj.1
      kan_have htail := hconj.2
      kan_rw [heq]
      kan_have ihres := ih htail
      kan_simp_only [Fin.lt_def] at ihres
      kan_linarith

theorem ofDigitsBE'_mono {r : Radix} {l₁ l₂ : List (Digit r)} :
    l₁.length = l₂.length → l₁ < l₂ → ofDigitsBE' l₁ < ofDigitsBE' l₂ := by
  kan_intro hl
  kan_intro hlt
  kan_have hres := ofDigitsBE_mono (l₁ := ⟨l₁, hl⟩) (l₂ := ⟨l₂, rfl⟩) hlt
  kan_simp_only [Fin.lt_def] at hres
  kan_have eq₁ :=
    ofDigitsBE'_toList (l := (⟨l₁, hl⟩ : List.Vector (Digit r) l₂.length))
  kan_have eq₂ :=
    ofDigitsBE'_toList (l := (⟨l₂, rfl⟩ : List.Vector (Digit r) l₂.length))
  kan_simp_only [List.Vector.toList_mk] at eq₁
  kan_simp_only [List.Vector.toList_mk] at eq₂
  kan_rw [eq₁, eq₂]
  kan_exact hres

theorem ofDigitsBE'_subtype_eq {r : Radix} {l : List.Vector (Digit r) d}
    (hlt : ofDigitsBE' l.toList < r.val ^ d) :
    (⟨ofDigitsBE' l.toList, hlt⟩ : RadixVec r d) = ofDigitsBE l := by
  kan_apply Fin.eq_of_val_eq
  kan_exact ofDigitsBE'_toList

end RadixVec

def toBaseLE (B n v : Nat) : List Nat :=
  match n with
  | 0 => []
  | n + 1 => v % B :: toBaseLE B n (v / B)

@[simp]
lemma toBaseLE_len : (toBaseLE B n v).length = n := by
  kan_induction_with n generalizing v with
  | zero => kan_rfl
  | succ n ih =>
    kan_simp [toBaseLE, ih]

theorem toBaseLE_succ_snoc :
    toBaseLE B (n + 1) v = toBaseLE B n v ++ [(v / B ^ n) % B] := by
  kan_induction_with n generalizing v with
  | zero =>
    kan_simp [toBaseLE]
  | succ n ih =>
    kan_conv_lhs rw [toBaseLE]
    kan_rw [ih]
    kan_conv_rhs rw [toBaseLE]
    kan_simp_only [List.cons_append]
    kan_congr 1
    kan_congr 1
    kan_simp [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem toBaseLE_take : (toBaseLE B n v).take m = toBaseLE B (min m n) v := by
  kan_induction_with m generalizing v n with
  | zero =>
    kan_simp [Nat.zero_min, toBaseLE]
  | succ m ih =>
    kan_cases_with n with
    | zero => kan_simp [toBaseLE]
    | succ n => kan_simp [toBaseLE, Nat.succ_min_succ, ih]

private theorem toBaseLE_drop_aux (B : Nat) (d m : Nat) (v : Nat) :
    (toBaseLE B (d + m) v).drop m = toBaseLE B d (v / B ^ m) := by
  kan_induction_with m generalizing v with
  | zero =>
    kan_simp
  | succ m ih =>
    kan_rw [<-add_assoc]
    kan_simp_at ih
    kan_simp [toBaseLE, ih, Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem toBaseLE_drop : (toBaseLE B n v).drop m = toBaseLE B (n - m) (v / B ^ m) := by
  kan_by_cases h : m ≤ n
  · kan_conv_lhs rw [show n = (n - m) + m from (Nat.sub_add_cancel h).symm]
    kan_exact toBaseLE_drop_aux B (n - m) m v
  · kan_have hlt : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_le h)
    kan_have t₁ : n - m = 0 := Nat.sub_eq_zero_of_le hlt
    kan_rw [t₁]
    kan_have rhs_eq : toBaseLE B 0 (v / B ^ m) = ([] : List Nat) := rfl
    kan_rw [rhs_eq]
    kan_apply List.drop_of_length_le
    kan_rw [toBaseLE_len]
    kan_exact hlt

def ofBaseLE (B : Nat) (v : List Nat) : Nat :=
  v.foldr (fun bit rest => bit + B * rest) 0

theorem ofBaseLE_toBaseLE : ofBaseLE B (toBaseLE B D N) = N % B ^ D := by
  kan_induction_with D generalizing N with
  | zero => kan_simp [Nat.mod_one, toBaseLE, ofBaseLE]
  | succ D ih =>
    kan_simp [ofBaseLE] at ih
    kan_simp [toBaseLE, ofBaseLE]
    kan_rw [ih, add_comm, Nat.pow_succ]
    kan_conv rhs; rw [mul_comm, Nat.mod_mul, add_comm]

theorem ofBaseLE_toBaseLE_of_lt (h : N < B ^ D) : ofBaseLE B (toBaseLE B D N) = N := by
  kan_rw [ofBaseLE_toBaseLE, Nat.mod_eq_of_lt h]

theorem toBaseLE_pow {B D K N} :
    toBaseLE (B ^ D) K N =
      (toBaseLE B (K * D) N |>.chunksExact D (by kan_simp; kan_exact Or.inl rfl) |>.map (ofBaseLE B)) := by
  kan_induction_with K generalizing N with
  | zero =>
    kan_simp [toBaseLE, List.chunksExact]
  | succ K ih =>
    kan_simp_only [toBaseLE, ih, List.Vector.map_cons, Nat.succ_mul]
    kan_congr 1
    · kan_simp [toBaseLE_take, ofBaseLE_toBaseLE]
    · kan_congr
      kan_simp [toBaseLE_drop]

lemma toBaseLE_elem_lt {B n i j : Nat} [hnz : NeZero B] {h} :
    (toBaseLE B n i)[j]'h < B := by
  kan_induction_with n generalizing i j with
  | zero =>
    kan_simp [toBaseLE]
    kan_contradiction
  | succ n ih =>
    kan_simp [toBaseLE]
    kan_cases_with j with
    | zero =>
      kan_simp
      kan_apply Nat.mod_lt
      kan_apply Nat.zero_lt_of_ne_zero
      kan_exact hnz.ne
    | succ j => kan_simp [ih]

lemma ofBaseLE_append :
    ofBaseLE B (a ++ b) = ofBaseLE B a + B ^ a.length * ofBaseLE B b := by
  kan_induction_with a with
  | nil => kan_simp [ofBaseLE]
  | cons h t ih =>
    kan_simp_only [ofBaseLE] at ih
    kan_simp_only [
      ofBaseLE, List.map, List.cons_append, List.foldr_cons, ih, List.length_cons, pow_succ
    ]
    kan_linarith

end KanLampe
