import Lake
open Lake DSL

require evmyul from git
  "https://github.com/NethermindEth/EVMYulLean.git" @ "main"

package «evm-compiler» {
  moreLeanArgs := #["-DautoImplicit=false"]
  moreServerOptions := #[⟨`autoImplicit, false⟩]
}

@[default_target]
lean_lib «EvmCompiler»

