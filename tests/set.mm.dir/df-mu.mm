
axiom df-mu
  let vx: setvar x
  let vp: setvar p
  assert |- mmu = ( x e. NN |-> if ( E. p e. Prime ( p ^ 2 ) || x , 0 , ( -u 1 ^ ( # ` { p e. Prime | p || x } ) ) ) )
end
