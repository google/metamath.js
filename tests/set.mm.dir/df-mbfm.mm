
axiom df-mbfm
  let vx: setvar x
  let vt: setvar t
  let vf: setvar f
  let vs: setvar s
  assert |- MblFnM = ( s e. U. ran sigAlgebra , t e. U. ran sigAlgebra |-> { f e. ( U. t ^m U. s ) | A. x e. t ( `' f " x ) e. s } )
end
