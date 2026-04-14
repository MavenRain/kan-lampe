import KanLampe.SeparationLogic.LawfulHeap
import KanLampe.SeparationLogic.ValHeap
import KanLampe.Ast

/-!
# KanLampe.SeparationLogic.State

Port of `Lampe.SeparationLogic.State`.  Defines the `State` of a
program (`ValHeap` together with a `Lambdas` map), installs the
`LawfulHeap` instance, and provides the value / lambda singleton
separation-logic predicates and the structural union lemmas.
-/

namespace KanLampe

abbrev Lambdas (p : Prime) := Finmap fun _ : Ref => Lambda (Tp.denote p)

structure State (p : Prime) where
  vals : ValHeap p
  lambdas : Lambdas p

variable {p : Prime} {T : Type}

instance : Membership Ref (State p) where
  mem := fun a e => e ∈ a.vals

@[simp]
lemma State.membership_in_val {a : State p} {e : Ref} : e ∈ a ↔ e ∈ a.vals := by
  kan_exact Iff.rfl

instance : Coe (State p) (ValHeap p) where
  coe := fun s => s.vals

/-- Maps a post-condition on `State`s to a post-condition on `ValHeap`s
by keeping the lambdas fixed. -/
@[reducible]
def mapToValHeapCondition
    (lambdas : Lambdas p)
    (Q : Option (State p × T) → Prop) : Option (ValHeap p × T) → Prop :=
  fun vv => Q (vv.map (fun (vals, t) => ⟨⟨vals, lambdas⟩, t⟩))

/-- Maps a post-condition on `ValHeap`s to a post-condition on `State`s. -/
@[reducible]
def mapToStateCondition
    (Q : Option (ValHeap p × T) → Prop) : Option (State p × T) → Prop :=
  fun stv => Q (stv.map (fun (st, t) => ⟨st.vals, t⟩))

def State.insertVal (self : State p) (r : Ref) (v : AnyValue p) : State p :=
  ⟨self.vals.insert r v, self.lambdas⟩

lemma State.eq_constructor {st₁ st₂ : State p} :
    (st₁ = st₂) ↔ (State.mk st₁.vals st₁.lambdas = State.mk st₂.vals st₂.lambdas) := by
  kan_exact Iff.rfl

@[simp]
lemma State.eq_closures {v v' : ValHeap p} {c c' : Lambdas p} :
    (State.mk v c = State.mk v' c') → (c = c') := by
  kan_intro h
  kan_cases h
  kan_rfl

instance : LawfulHeap (State p) where
  union := fun a b => ⟨a.vals ∪ b.vals, a.lambdas ∪ b.lambdas⟩
  disjoint := fun a b => a.vals.Disjoint b.vals ∧ a.lambdas.Disjoint b.lambdas
  empty := ⟨∅, ∅⟩
  thm_union_empty := by
    kan_intro a
    kan_simp_all [Finmap.union_empty]
  thm_union_assoc := by
    kan_intro s₁
    kan_intro s₂
    kan_intro s₃
    kan_simp_only [Union.union, State.mk.injEq]
    kan_constructor
    · kan_apply Finmap.union_assoc
    · kan_apply Finmap.union_assoc
  thm_disjoint_symm_iff := by
    kan_simp_all [Finmap.Disjoint.symm_iff, and_comm]
  thm_union_comm_of_disjoint := by
    kan_intro s₁
    kan_intro s₂
    kan_intro hdis
    kan_simp_only [Union.union, State.mk.injEq]
    kan_cases hdis
    kan_constructor
    · kan_apply Finmap.union_comm_of_disjoint
      kan_assumption
    · kan_apply Finmap.union_comm_of_disjoint
      kan_assumption
  thm_disjoint_empty := by
    kan_intro x
    kan_constructor
    · kan_apply Finmap.disjoint_empty
    · kan_apply Finmap.disjoint_empty
  thm_disjoint_union_left := by
    kan_intro x
    kan_intro y
    kan_intro z
    kan_rw [Finmap.disjoint_union_left x.vals y.vals z.vals,
            Finmap.disjoint_union_left x.lambdas y.lambdas z.lambdas]
    kan_constructor
    · kan_intro h
      kan_exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩
    · kan_intro h
      kan_exact ⟨⟨h.1.1, h.2.1⟩, ⟨h.1.2, h.2.2⟩⟩

@[reducible]
def State.valSingleton (r : Ref) (v : AnyValue p) : SLP (State p) :=
  fun st => st.vals = Finmap.singleton r v

notation:max "[ " l " ↦ " r " ]" => State.valSingleton l r

@[reducible]
def State.lmbSingleton {argTps : List Tp} {outTp : Tp}
    (r : FuncRef argTps outTp)
    (f : HList (Tp.denote p) argTps → Expr (Tp.denote p) outTp) : SLP (State p) :=
  fun st => ∃ rr, r = FuncRef.lambda rr ∧ st.lambdas = Finmap.singleton rr ⟨argTps, outTp, f⟩

notation:max "[λ " r " ↦ " f " ]" => State.lmbSingleton r f

@[simp]
lemma State.union_parts_left {v : ValHeap p} {c : Lambdas p} {st₂ : State p} :
    (State.mk v c ∪ st₂ = State.mk (v ∪ st₂.vals) (c ∪ st₂.lambdas)) := by
  kan_rfl

@[simp]
lemma State.union_parts_right {v : ValHeap p} {c : Lambdas p} {st₂ : State p} :
    (st₂ ∪ State.mk v c = State.mk (st₂.vals ∪ v) (st₂.lambdas ∪ c)) := by
  kan_rfl

@[simp]
lemma State.union_parts {st₁ st₂ : State p} :
    st₁ ∪ st₂ = State.mk (st₁.vals ∪ st₂.vals) (st₁.lambdas ∪ st₂.lambdas) := by
  kan_rfl

@[simp]
lemma State.union_vals {st₁ st₂ : State p} :
    (st₁ ∪ st₂).vals = (st₁.vals ∪ st₂.vals) := by
  kan_rfl

@[simp]
lemma State.union_closures {st₁ st₂ : State p} :
    (st₁ ∪ st₂).lambdas = (st₁.lambdas ∪ st₂.lambdas) := by
  kan_rfl

end KanLampe
