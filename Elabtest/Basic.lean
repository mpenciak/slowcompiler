import Lean

open Lean

inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v) where
| nil : HList β []
| cons : ∀ {a : α} {as : List α}, β a → HList β as → HList β (a :: as)

syntax "h![" term,* "]" : term
macro_rules
| `(h![]) => `(HList.nil)
| `(h![$x]) => `(HList.cons $x HList.nil)
| `(h![$x, $xs,*]) => `(HList.cons $x h![$xs,*])

def makeHListLit {m} [Monad m] [MonadQuotation m] : List (TSyntax `term) → m (TSyntax `term)
  | xs => `(h![$xs.toArray,*])

inductive Tp | unit | array (n : Nat) (elem : Tp)

inductive Val (rep : Tp → Type) : Tp → Type where
| unit : Val rep .unit
| array : (v : Vector (rep elemTp) n) → Val rep (elemTp.array n)
| letIn : Val rep t₁ → (rep t₁ → Val rep t₂) → Val rep t₂
| call : (argTps : List Tp) → (outTp : Tp) → (args : HList rep argTps) → Val rep outTp

structure Lambda (rep : Tp → Type) where
  argTps : List Tp
  outTp : Tp
  body : HList rep argTps → Val rep outTp

structure Function where
  body : ∀ (rep : Tp → Type), Lambda rep

structure DSLState where
  nextFresh : Nat

class MonadDSL (m : Type → Type) extends Monad m, MonadQuotation m, MonadStateOf DSLState m

@[default_instance]
instance {m} [Monad m] [MonadQuotation m] [MonadStateOf DSLState m] : MonadDSL m where

def MonadDSL.run [Monad m] [MonadQuotation m] (a : StateT DSLState m α) : m α :=
  StateT.run' a ⟨0⟩

def nameOf {m} [MonadDSL m] : m Lean.Ident :=
  modifyGet fun s =>
    (mkIdent (.mkSimple s!"#v_{s.nextFresh}"), { s with nextFresh := s.nextFresh.succ })

def wrapInLet {m} [MonadDSL m] (e : TSyntax `term) (k : Option $ TSyntax `term → m (TSyntax `term))
    : m (TSyntax `term) := do
  let ident ← nameOf
  match k with
  | some k => do
    let rest ← k ident
    ``(Val.letIn $e fun $ident => $rest)
  | none => do
    pure e

def makeBlock {m} [MonadDSL m] (fuel : Nat) (k : Option $ TSyntax `term → m (TSyntax `term))
  : m (TSyntax `term) := do
  match fuel with
  | n + 1 => wrapInLet (←``(Val.unit)) $ some fun _ => makeBlock n k
  | 0 =>
    let ⟨numBinders⟩ ← get
    let names := List.range numBinders |>.map (fun i => ⟨mkIdent (.mkSimple s!"#v_{i}")⟩)
    let args ← makeHListLit names
    wrapInLet (←``(Val.call _ (Tp.array 0 Tp.unit) $args)) k

def makeWeirdExpr {m} [MonadDSL m] (fuel : Nat) : m (TSyntax `term) := do
  makeBlock fuel none

open Elab.Command in
elab "#foo" : command => do
  let body ← MonadDSL.run $ makeWeirdExpr 50
  let lambda ← `(fun rep => ⟨[], _, fun args => match args with | h![] => $body⟩)
  let func ← ``(Function.mk $lambda)
  let decl ← `(def $(mkIdent `foo) : Function := $func)
  elabCommand decl

#foo
