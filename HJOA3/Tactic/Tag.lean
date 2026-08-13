module

public meta import Lean.Elab.Command
public import Mathlib.Init

/-!
# The `hjoa3` attribute
-/

public meta section

open Lean Elab

namespace HJOA3.Tag

/--
A single `hjoa3` pairing: the tagged declaration, the blueprint entity's LaTeX label, and an
optional comment supplied with the attribute.
-/
structure Entry where
  /-- The name of the declaration carrying this tag. -/
  declName : Name
  /-- The blueprint entity's LaTeX `\label`, verbatim — e.g. -/
  tag : String
  /-- An optional comment supplied with the attribute; empty when omitted. -/
  comment : String := ""
  deriving BEq, Hashable

/-- Persistent environment extension holding every `hjoa3` pairing visible to the current build. -/
initialize tagExt : SimplePersistentEnvExtension Entry (Array (Array Entry)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn tags := tags
    addEntryFn tags _ := tags
  }

/-- Register the pairing `(declName, tag, comment)` with `tagExt`. -/
def addEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) (tag : String) (comment : String := "") : m Unit :=
  modifyEnv (tagExt.addEntry · { declName, tag, comment })

/-- Every `hjoa3` pairing in the environment, imported entries first. -/
def entries (env : Environment) : Array Entry :=
  let state := PersistentEnvExtension.getState tagExt env
  state.2.flatten.appendList state.1

/-- The `hjoa3` attribute. -/
syntax (name := hjoa3Tag) "hjoa3" ppSpace str (ppSpace str)? : attr

initialize Lean.registerBuiltinAttribute {
  name := `hjoa3Tag
  descr := "Mark a Lean declaration as formalizing an HJOA3 blueprint entity."
  add := fun decl stx _attrKind => do
    let (tag, comment) ← match stx with
      | `(attr| hjoa3 $tag:str $[$comment:str]?) =>
        pure (tag.getString, (comment.map (·.getString)).getD "")
      | _ => throwUnsupportedSyntax
    addEntry decl tag comment
}

/--
Tag a declaration this repo does not own — an QSeriesLib or Mathlib result that already proves
a blueprint entity — without editing the file that declares it:
-/
syntax (name := addToHjoa3)
  "add_to_hjoa3" ppSpace str (ppSpace str)? ppSpace ident : command

/-- Elaborator for the `add_to_hjoa3` command. -/
@[command_elab addToHjoa3]
def addToHjoa3Elab : Command.CommandElab := fun stx ↦ match stx with
  | `(command| add_to_hjoa3 $tag:str $[$comment:str]? $declStx:ident) => do
    let tagStr := tag.getString
    let commentStr := (comment.map (·.getString)).getD ""
    let declList ← Command.liftCoreM <| resolveGlobalConst declStx
    let [decl] := declList
      | throwError m!"Ambiguous identifier: {declList}"
    Command.runTermElabM fun _ ↦ do
      Term.addTermInfo' declStx (← Meta.mkConstWithFreshMVarLevels decl)
    if (entries (← Command.liftCoreM getEnv)).any
        fun e => e.declName == decl && e.tag == tagStr then
      logWarningAt stx
        m!"'{decl}' already carries the hjoa3 tag {tagStr}; skipping duplicate."
    Command.liftCoreM <| addEntry decl tagStr commentStr
  | _ => throwUnsupportedSyntax

/--
`#hjoa3_tags` lists every declaration carrying an `hjoa3` tag in the current environment,
ordered by tag.
-/
elab (name := hjoa3TagsCmd) "#hjoa3_tags" : command => do
  let sorted := (entries (← Command.liftCoreM getEnv)).qsort (fun a b => a.tag < b.tag)
  if sorted.isEmpty then
    logInfo "No hjoa3 tags found."
  else
    let mut msgs := #[m!""]
    for e in sorted do
      let cmt := if e.comment = "" then "" else s!" ({e.comment})"
      msgs := msgs.push
        m!"[{e.tag}{cmt}] corresponds to declaration '{.ofConstName e.declName}'."
    logInfo (MessageData.joinSep msgs.toList "\n")

end HJOA3.Tag
