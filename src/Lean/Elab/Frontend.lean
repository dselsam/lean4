/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Elab.Import
import Lean.Elab.Command
import Lean.Util.Profile

namespace Lean.Elab.Frontend

structure State where
  commandState : Command.State
  parserState  : Parser.ModuleParserState
  cmdPos       : String.Pos
  commands     : Array Syntax := #[]

structure Context where
  inputCtx : Parser.InputContext

abbrev FrontendM := ReaderT Context $ StateRefT State IO

def setCommandState (commandState : Command.State) : FrontendM Unit :=
  modify fun s => { s with commandState := commandState }

@[inline] def runCommandElabM (x : Command.CommandElabM Unit) : FrontendM Unit := do
  let ctx ← read
  let s ← get
  let cmdCtx : Command.Context := { cmdPos := s.cmdPos, fileName := ctx.inputCtx.fileName, fileMap := ctx.inputCtx.fileMap }
  let sNew? ← liftM $ EIO.toIO (fun _ => IO.Error.userError "unexpected error") (do let (_, s) ← (x cmdCtx).run s.commandState; pure $ some s)
  match sNew? with
  | some sNew => setCommandState sNew
  | none      => pure ()

def elabCommandAtFrontend (stx : Syntax) : FrontendM Unit := do
  runCommandElabM (Command.elabCommand stx)

def updateCmdPos : FrontendM Unit := do
  modify fun s => { s with cmdPos := s.parserState.pos }

def getParserState : FrontendM Parser.ModuleParserState := do pure (← get).parserState
def getCommandState : FrontendM Command.State := do pure (← get).commandState
def setParserState (ps : Parser.ModuleParserState) : FrontendM Unit := modify fun s => { s with parserState := ps }
def setMessages (msgs : MessageLog) : FrontendM Unit := modify fun s => { s with commandState := { s.commandState with messages := msgs } }
def getInputContext : FrontendM Parser.InputContext := do pure (← read).inputCtx

def showSourceInfo : SourceInfo → String
| SourceInfo.original leading pos trailing => "(original {leading} {pos} {trailing})"
| SourceInfo.synthetic pos endPos          => "(synthetic {pos} {endPos})"
| SourceInfo.none                          => "(none)"

partial def showSyntax : Syntax → String
| Syntax.missing               => "(missing)"
| Syntax.node kind args        => s!"(node {kind} #[{",".intercalate (args.map showSyntax).toList}])"
| Syntax.atom info val  => s!"(atom {showSourceInfo info} {val})"
| Syntax.ident info rawval val prs => s!"(ident {showSourceInfo info} {rawval} {val} {prs})"

def processCommand : FrontendM Bool := do
  updateCmdPos
  let cmdState ← getCommandState
  let ictx ← getInputContext
  let pstate ← getParserState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let pos := ictx.fileMap.toPosition pstate.pos
  match profileit "parsing" scope.opts pos fun _ => Parser.parseCommand ictx pmctx pstate cmdState.messages with
  | (cmd, ps, messages) =>
    modify fun s => { s with commands := s.commands.push cmd }
    setParserState ps
    setMessages messages
    if Parser.isEOI cmd || Parser.isExitCommand cmd then
      pure true -- Done
    else
      -- START TEMP
      -- println! "[COMMAND] {showSyntax cmd}"
      -- END TEMP
      profileitM IO.Error "elaboration" scope.opts pos $ elabCommandAtFrontend cmd
      pure false

partial def processCommands : FrontendM Unit := do
  let done ← processCommand
  unless done do
    processCommands

end Frontend

open Frontend

def IO.processCommands (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState) (commandState : Command.State) : IO State := do
  let (_, s) ← (Frontend.processCommands.run { inputCtx := inputCtx }).run { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }
  pure s

def process (input : String) (env : Environment) (opts : Options) (fileName : Option String := none) : IO (Environment × MessageLog) := do
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let s ← IO.processCommands inputCtx { : Parser.ModuleParserState } (Command.mkState env {} opts)
  pure (s.commandState.env, s.commandState.messages)

builtin_initialize
  registerOption `printMessageEndPos { defValue := false, descr := "print end position of each message in addition to start position" }

def getPrintMessageEndPos (opts : Options) : Bool :=
  opts.getBool `printMessageEndPos false

@[export lean_run_frontend]
def runFrontend (input : String) (opts : Options) (fileName : String) (mainModuleName : Name) : IO (Environment × Bool) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx
  let env := env.setMainModule mainModuleName
  let s ← IO.processCommands inputCtx parserState (Command.mkState env messages opts)
  for msg in s.commandState.messages.toList do
    IO.print (← msg.toString (includeEndPos := getPrintMessageEndPos opts))
  pure (s.commandState.env, !s.commandState.messages.hasErrors)

end Lean.Elab
