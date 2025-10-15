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

def Tp.denote : Tp → Type
| unit => Unit
| array n elem => Vector elem.denote n

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

declare_syntax_cat decl
declare_syntax_cat expr

syntax (name := myDef) "my_def" ident ":=" expr : command
syntax "{" sepBy(expr, ";") "}": expr
syntax "mkArray(" expr,* ")" : expr
syntax "#unit" : expr

class MonadUtil (m : Type → Type) extends Monad m, MonadQuotation m, MonadExceptOf Exception m, MonadError m

@[default_instance]
instance {m} [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m] : MonadUtil m where

structure DSLState where
  nextFresh : Nat

class MonadDSL (m : Type → Type) extends MonadUtil m, MonadStateOf DSLState m

@[default_instance]
instance {m} [MonadUtil m] [MonadStateOf DSLState m] : MonadDSL m where

def MonadDSL.run [Monad m] [MonadQuotation m] [MonadExceptOf Exception m] [MonadError m]
    (a : StateT DSLState m α) : m α :=
  StateT.run' a ⟨0⟩

def nameOf {m} [MonadDSL m] : Option Lean.Ident → m Lean.Ident
| none =>
  modifyGet fun s =>
  (mkIdent (.mkSimple s!"#v_{s.nextFresh}"), { s with nextFresh := s.nextFresh.succ })
| some n => pure n

def wrapInLet {m} [MonadDSL m]
    (e : TSyntax `term)
    (ident : Option Lean.Ident)
    (k : Option $ TSyntax `term → m (TSyntax `term))
  : m (TSyntax `term) := do
  let ident ← nameOf ident
  match k with
  | some k => do
    let rest ← k ident
    ``(Val.letIn $e fun $ident => $rest)
  | none => do
    pure e

open Elab

mutual

partial def makeBlock {m} [MonadDSL m]
    (items : List (TSyntax `expr))
    (binder : Option Lean.Ident)
    (k : Option $ TSyntax `term → m (TSyntax `term))
  : m (TSyntax `term) := match items with
| head :: next :: rest => do
  match head with
  | e => do makeExpr e none $ some fun _ => makeBlock (next :: rest) binder k
| [last] => makeExpr last binder k
| _ => throwError "Empty blocks are invalid"

partial def makeExpr {m} [MonadDSL m]
    (expr : TSyntax `expr)
    (binder : Option Lean.Ident)
    (k : Option (TSyntax `term → m (TSyntax `term))) : m (TSyntax `term) := do
  match expr with
  | `(expr|#unit) => do wrapInLet (←``(Val.unit)) binder k
  | `(expr|{ $exprs;* }) => do
    let block ← makeBlock exprs.getElems.toList binder none
    wrapInLet block binder k
  | `(expr|mkArray( $args,* )) =>
    makeArgs args.getElems.toList fun args => do
      let argVals ← makeHListLit args
      wrapInLet
        (←``(Val.call _ (Tp.array 0 Tp.unit) $argVals))
        binder
        k
  | _ => throwUnsupportedSyntax

partial def makeArgs {m} [MonadDSL m]
    (args : List (TSyntax `expr))
    (k : List (TSyntax `term) → m (TSyntax `term))
  : m (TSyntax `term) := match args with
| [] => k []
| h :: t => makeExpr h none (some fun h => makeArgs t fun t => k (h :: t))

end

open Command

@[command_elab myDef]
def elabMyDef : CommandElab := fun stx =>
  match stx with
| `(my_def $id:ident := $body:expr) => do
  let body ← MonadDSL.run do
    makeExpr body none none

  let lambda ← `(fun rep => {
        argTps := [],
        outTp := .unit,
        body := fun args => match args with
          | h![] => $body
      }
    )

  let func ← ``(Function.mk $lambda)
  let decl ← `(def $id : Function := $func)
  elabCommand decl
| _ => throwUnsupportedSyntax


-- set_option trace.profiler.threshold 3
-- set_option trace.profiler true
-- set_option trace.Compiler.elimDeadBranches true
-- set_option maxHeartbeats 10000000

my_def asdf := {
  mkArray(
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit,
    #unit, #unit, #unit, #unit
  );
  #unit
}

#print asdf
