
axiom df-inag
  let vx: setvar x
  let vt: setvar t
  let vg: setvar g
  let vp: setvar p
  assert |- inA = ( g e. _V |-> { <. p , t >. | ( ( p e. ( Base ` g ) /\ t e. ( ( Base ` g ) ^m ( 0 ..^ 3 ) ) ) /\ ( ( ( t ` 0 ) =/= ( t ` 1 ) /\ ( t ` 2 ) =/= ( t ` 1 ) /\ p =/= ( t ` 1 ) ) /\ E. x e. ( Base ` g ) ( x e. ( ( t ` 0 ) ( Itv ` g ) ( t ` 2 ) ) /\ ( x = ( t ` 1 ) \/ x ( ( hlG ` g ) ` ( t ` 1 ) ) p ) ) ) ) } )
end
