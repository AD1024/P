/-
PLean.Semantics.PSet — first-order set theory for P's `set[T]`.

`Set α = α → Prop` is a transparent function type: membership `x ∈ s`
is *defeq* the application `s x`, which lean-auto reads as an anonymous
function atom and rejects (`Set X is not a ∀`), or — when membership
co-occurs with `Eq` on the element type — trips its verified reifier
(`reifTermCheckType … is not type correct`). Neither face is our bug to
fix; both are avoided by giving membership a *symbol*.

`PSet` is that symbol. The type and its operations are ordinary `def`s
over the `Set`-backed model, so every spec lemma below is a THEOREM
(the trusted base gains no axiom). The final `attribute [irreducible]`
seals the type and ops: after sealing, lean-auto's whnf can no longer
peel `PSet.mem x s` back to `s x`, so it translates `PSet.mem` as an
uninterpreted binary relation and `PSet α` as an uninterpreted sort —
the shape UCLID5/PVerifier use for sets. Same seal-after-prove pattern
`#gen_module` applies to `<ev>_payload_of`.
-/
import PLean.Verify.SimpAttrs

namespace PLean

/-- `PSet α` — P's `set[T]`, as a first-order sort. Backed by `α → Prop`
until sealed `irreducible` at the end of this file. -/
def PSet (α : Type) : Type := α → Prop

namespace PSet

variable {α : Type}

/-- Membership relation. Uninterpreted after sealing. -/
def mem (x : α) (s : PSet α) : Prop := s x

/-- The empty set. -/
def empty : PSet α := fun _ => False

/-- Insert an element. -/
def insert (a : α) (s : PSet α) : PSet α := fun x => x = a ∨ s x

/-- Remove an element. Backs the `-=` mutation on sets. -/
def erase (a : α) (s : PSet α) : PSet α := fun x => x ≠ a ∧ s x

end PSet

/-- `x ∈ s` for `s : PSet α` is the membership relation. -/
instance instMembershipPSet {α : Type} : Membership α (PSet α) where
  mem s x := PSet.mem x s

/-- `default(set[T])` and the `Fields`/`Containers` `deriving Inhabited`
resolve to the empty set. -/
instance instInhabitedPSet {α : Type} : Inhabited (PSet α) := ⟨PSet.empty⟩

/-- `s += (e)` desugars to `Insert.insert e s`; dispatch it to
`PSet.insert` so the surface mutation macro works unchanged. -/
instance instInsertPSet {α : Type} : Insert α (PSet α) := ⟨PSet.insert⟩

/-- `s x` (set-as-predicate application — the `n.votes a` invariant
idiom) reads as membership. Lets the surface keep P's applicative
membership without a rewrite. -/
instance instCoeFunPSet {α : Type} : CoeFun (PSet α) (fun _ => α → Prop) where
  coe s x := PSet.mem x s

namespace PSet

variable {α : Type}

/-! ## Spec lemmas — THEOREMS over the model, tagged `@[pverifySimp]`.

Each holds by `rfl`/`Iff.rfl` while the ops are transparent; the seal
below turns the LHS into an opaque symbol that SMT prep rewrites via
these lemmas. -/

/-- `∈` unfolds to the `mem` relation. Bridges the surface `x ∈ s` and
`s x` idioms to the single opaque symbol before translation. -/
@[pverifySimp] theorem mem_def (x : α) (s : PSet α) :
    (x ∈ s) = PSet.mem x s := rfl

/-- The `CoeFun` application `s x` is the same `mem` relation. -/
@[pverifySimp] theorem coe_apply (s : PSet α) (x : α) :
    (s : α → Prop) x = PSet.mem x s := rfl

/-- Nothing is a member of the empty set. -/
@[pverifySimp] theorem mem_empty (x : α) : ¬ PSet.mem x (PSet.empty) := id

/-- Membership after insert: the inserted element or a prior member. -/
@[pverifySimp] theorem mem_insert (x a : α) (s : PSet α) :
    PSet.mem x (PSet.insert a s) ↔ (x = a ∨ PSet.mem x s) := Iff.rfl

/-- Membership after erase: a prior member other than the erased one. -/
@[pverifySimp] theorem mem_erase (x a : α) (s : PSet α) :
    PSet.mem x (PSet.erase a s) ↔ (x ≠ a ∧ PSet.mem x s) := Iff.rfl

/-- The surface `s += (e)` desugars to `Insert.insert e s`; bridge it to
`PSet.insert` so the `mem_insert` spec fires. Proven by `rfl` while the
`Insert` instance's projection still reduces. -/
@[pverifySimp] theorem insert_eq (a : α) (s : PSet α) :
    Insert.insert a s = PSet.insert a s := rfl

end PSet

-- Seal. Everything above is proven; nothing below may unfold these.
-- The `-=` bridge lives with the other container-erase instances in
-- `Semantics/Containers.lean`; it reduces `containerErase` to
-- `PSet.erase` by `rfl` (the instance projection unfolds), independent
-- of this seal.
attribute [irreducible] PSet PSet.mem PSet.empty PSet.insert PSet.erase

/-! ## Model adequacy

The seal hides the model but doesn't remove it: `PSet` is still `Set`-
faithful because each op/lemma was defined and proven over `α → Prop`
before sealing. These `example`s re-derive the specs *through the seal*
(so they'd fail if a later edit made a spec lemma unprovable), keeping
the "no new axioms" guarantee auditable. -/

namespace PSet

private example {α : Type} (x : α) : ¬ (x ∈ (PSet.empty : PSet α)) := by
  rw [mem_def]; exact mem_empty x

private example {α : Type} (x a : α) (s : PSet α) :
    (x ∈ PSet.insert a s) ↔ (x = a ∨ x ∈ s) := by
  rw [mem_def, mem_def]; exact mem_insert x a s

end PSet

end PLean
