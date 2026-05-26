import Lake
open Lake DSL

require evmyul from git
  "https://github.com/danrobinson/EVMYulLean.git" @ "codex/chain-call-semantics"

package «evm-compiler» {
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]
}

@[default_target]
lean_lib «EvmCompiler»
