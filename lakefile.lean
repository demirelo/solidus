import Lake
open Lake DSL

require evmyul from git
  "https://github.com/danrobinson/EVMYulLean.git" @ "a959211f5d8dcda45185e9938573cac510244ba0"

package «evm-compiler» {
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]
}

@[default_target]
lean_lib «EvmCompiler»
