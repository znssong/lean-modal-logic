/-
This code uses a modified version of Lean compiler, so it can't be compiled using official Lean 4 releases.
The modification is following:
In file `src/Lean/Meta/SynthInstance.lean`, between code line `let type ← preprocess type` and line
`let cacheKey := { localInsts, type, synthPendingDepth := (← read).synthPendingDepth }`,
we added the following code snippet:
```lean
    let resultFromParam ← forallTelescopeReducing type fun xs type => do
      let paramTypes ← xs.mapM inferType
      let n := paramTypes.size
      if let some i := paramTypes.reverse.findIdx? (· == type) then
        return some (← mkLambdaFVars xs xs[n - 1 - i]!)
      else
        return none
    if let some result := resultFromParam then
      trace[Meta.synthInstance] "result already in the parameters of type {type}, result is {result}"
      return some result
```
Note that the indent is 4 spaces, to be aligned with the former line `let type ← preprocess type`.
-/
import Lean
import Mathlib.Tactic

open Lean.PrettyPrinter Delaborator

@[class] axiom World : Type
axiom Accessible : World → World → Prop
@[instance] axiom equiv_acc : IsEquiv World Accessible

variable [w : World]

set_option linter.unusedVariables false in
def ofWorld (α : [World] → Type _) := ∀ [w : World], α
notation:max "&" t => ofWorld (fun [World] => t)
@[delab lam] def delabFunWorld : Delab := do
  let stx ← delabLam
  match stx with
  | `(fun [World] => $P) => `($P)
  | `(fun [World] $p* => $P) => `(fun $p* => $P)
  | _ => return stx
@[delab forallE] def delabForallObject : Delab := do
  let stx ← delabForall
  match stx with
  | `(∀ [$_ : World], $p) => `($p)
  | `(∀ [$_ : World] $p*, $P) => `(∀$p*, $P)
  | `(∀ ($x : Object), $p) => `(∀$(⟨x⟩), $p)
  | _ => return stx

def atWorld {α : Type _} (w : World) (P : ofWorld α) : α := P (w := w)
notation t "@." w => atWorld w t
@[app_unexpander ofWorld] def unexpanderOfWorld : Unexpander
  | `($_ $x) => `(&$x)
  | _ => throw ()

def Necessary (p : &Prop) := ∀ w', Accessible w w' → p@.w'
def Possible (p : &Prop) := ∃ w', Accessible w w' ∧ p@.w'
notation "□" p:50 => Necessary p
notation "◇" p:50 => Possible p

axiom Object : &Type
def Property := &(Object → Prop)
axiom Positive : &(Property → Prop)
axiom positive_or_not : (P : Property) → Positive (fun x => ¬P x) ↔ ¬Positive P
axiom positive_imp {P : Property}
  (hP : Positive P) (Q : Property) : □(∀x, P x → Q x) → Positive Q

@[simp] lemma necessary_true : □True := by intro w'; simp [atWorld]
@[simp] lemma pos_true : Positive (fun _ => True) := by
  by_contra h
  apply h
  simp only [← positive_or_not, not_true_eq_false] at h
  exact positive_imp h (fun _ => True) (by simp)

@[simp] lemma not_pos_false : ¬Positive (fun _ => False) := by
  simp [← positive_or_not]

@[simp] lemma not_possible (p : &Prop) : ¬◇p ↔ □¬p := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  · simp [atWorld, Possible, Necessary] at h ⊢
    exact h

@[simp] lemma not_necessary (p : &Prop) : ¬□p ↔ ◇¬p := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp [atWorld, Possible, Necessary] at h
    obtain ⟨h, h', not⟩ := h
    exact ⟨h, h', not⟩
  · simp [atWorld, Possible, Necessary] at h ⊢
    exact h

theorem positive_possible_exists : ∀ {P}, Positive P → ◇∃ x, P x := by
  intro P pos
  by_contra h
  simp at h
  refine not_pos_false <| positive_imp pos (fun _ => False) ?_
  simpa using h

def God (x : Object) := ∀ {P}, Positive P → P x
axiom positive_God : Positive God
axiom positive_necessary : ∀ {P}, Positive P → □Positive P

lemma necessarize {p : &Prop} (hp : ∀ [World], p) : □p := fun _ _ => hp

theorem necessary_mp {p q : &Prop} : □(p → q) → □p → □q :=
  fun h hp w' acc => h w' acc (hp w' acc)

theorem possible_mp {p q : &Prop} : □(p → q) → ◇p → ◇q :=
  fun h ⟨w', acc, hp⟩ => ⟨w', acc, h w' acc hp⟩

def Essential (P : Property) (x : Object) := P x ∧ ∀ Q : Property, Q x → □∀ y, P y → Q y
theorem essential_God : ∀ {x}, God x → Essential God x := by
  intro x hx
  refine ⟨hx, fun Q hQ => ?_⟩
  have pos_Q : □Positive Q := by
    apply positive_necessary
    by_contra h
    rw [← positive_or_not] at h
    exact hx h hQ
  revert pos_Q
  apply necessary_mp
  exact fun w' _ pos y hy => hy pos

def NecessaryExistence (x : Object) := ∀ {P}, Essential P x → □∃y, P y
axiom positive_necessary_existence : Positive NecessaryExistence

lemma necessarily_exists_God : (∃x, God x) → □∃x, God x :=
  fun ⟨_, hx⟩ => hx positive_necessary_existence (essential_God hx)

lemma possible_necessary_imp {p : &Prop} : ◇□p → □p :=
  fun ⟨_, acc', h⟩ _ acc'' => h _ (_root_.trans (symm acc') acc'')

theorem God_exists : □∃x, God x :=
  possible_necessary_imp <|
    possible_mp
      (necessarize necessarily_exists_God)
      (positive_possible_exists positive_God)

#print axioms God_exists
