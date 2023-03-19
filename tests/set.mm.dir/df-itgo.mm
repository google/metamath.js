
axiom df-itgo
  let vx: setvar x
  let vs: setvar s
  let vp: setvar p
  assert |- IntgOver = ( s e. ~P CC |-> { x e. CC | E. p e. ( Poly ` s ) ( ( p ` x ) = 0 /\ ( ( coeff ` p ) ` ( deg ` p ) ) = 1 ) } )
end
