import Lake

open System Lake DSL

package «vector-commitments-lean» where version := v!"0.1.0"
require Velvet from git "https://github.com/verse-lab/velvet.git" @ "master"

@[default_target] lean_lib VectorCommitmentsLean
