# AGENTS.md

## Commands
- **Build**: `gleam build`
- **Type check**: `gleam check`
- **Run**: `gleam run` (runs main.gleam with candle/main.cd input)
- **Test**: `gleam test` (uses gleeunit)
- **Test single file**: `gleam test -- <test_name>`
- **Format**: `gleam format`
- **Dev**: `gleam dev`

## Architecture
- **candle_gleam**: A Cedille type checker/elaborator written in Gleam
- **Core modules**: elab.gleam (elaboration), parser.gleam (parsing), header.gleam (types/AST)
- **Input**: Reads .cd files from candle/ directory (main.cd)
- **Output**: Type checks and pretty-prints elaborated terms with their types
- **FFI**: JavaScript FFI in ffi.mjs for reference cells and ID generation

## Code Style
- **Imports**: Import modules first, then types/functions from header module
- **Naming**: snake_case for functions/variables, PascalCase for types/constructors
- **Error handling**: Use Result(a, String) for parsing/elaboration errors
- **Pattern matching**: Exhaustive case expressions, use `_` sparingly
- **Types**: Explicit type annotations for public functions
- **Comments**: Minimal, only for complex algorithms
