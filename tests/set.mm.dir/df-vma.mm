
axiom df-vma
  let vx: setvar x
  let vs: setvar s
  let vp: setvar p
  assert |- Lam = ( x e. NN |-> [_ { p e. Prime | p || x } / s ]_ if ( ( # ` s ) = 1 , ( log ` U. s ) , 0 ) )
end
