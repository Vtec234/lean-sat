import Lake
open Lake DSL

package LeanSat {
  defaultFacet := PackageFacet.oleans
  dependencies := #[
    { name := `mathlib3port, src := Source.git "https://github.com/leanprover-community/mathlib3port" "934a3b480a33f875231f5c5c18fdd5be0ea9755c" }
  ]
  -- add configuration options here
}
