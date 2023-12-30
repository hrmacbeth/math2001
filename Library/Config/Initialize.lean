/- Copyright (c) Mac Malone, 2023.  All rights reserved. -/
import Lean.Elab.ElabRules
open Lean Elab Command

/-- Apply the given option settings if the options exist. -/
def trySetOptions (settings : Array (Name × DataValue)) : CommandElabM PUnit := do
  let opts ← getOptions
  let ⟨_, opts⟩ ← StateT.run (s := opts) <| settings.forM fun ⟨optName, val⟩ => do
    if let .ok decl ← getOptionDecl optName |>.toBaseIO then
      unless decl.defValue.sameCtor val do
        throwError "type mismatch for '{optName}'"
      modify (·.insert optName val)
  modifyScope ({· with opts})

/-- Erase a set of declaration from the specified attributes if they both exist. -/
def tryEraseAttrs (attrs :  Array (Name × Array Name)) : CommandElabM PUnit := do
  liftCoreM <| attrs.forM fun ⟨attrName, declNames⟩ => do
    let attrState := attributeExtension.getState (← getEnv)
    if let some attr := attrState.map.find? attrName then
      declNames.forM fun declName =>
        try
          attr.erase declName
        catch _ =>
          -- This consumes all types of errors, rather than just existence ones,
          -- but there does not appear to be a better general way to achieve this
          pure ()
