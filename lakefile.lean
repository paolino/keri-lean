import Lake
open Lake DSL

package «keri-lean» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib KERI where
  srcDir := "."
