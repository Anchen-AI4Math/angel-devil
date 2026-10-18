import Lake
open Lake DSL
package «angel-devil» where
  leanOptions := #[⟨`autoImplicit, false⟩]
lean_lib Definitions
lean_lib Theorems
@[default_target]
lean_lib Solutions
