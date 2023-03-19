
axiom df-lfl
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vf: setvar f
  let vr: setvar r
  assert |- LFnl = ( w e. _V |-> { f e. ( ( Base ` ( Scalar ` w ) ) ^m ( Base ` w ) ) | A. r e. ( Base ` ( Scalar ` w ) ) A. x e. ( Base ` w ) A. y e. ( Base ` w ) ( f ` ( ( r ( .s ` w ) x ) ( +g ` w ) y ) ) = ( ( r ( .r ` ( Scalar ` w ) ) ( f ` x ) ) ( +g ` ( Scalar ` w ) ) ( f ` y ) ) } )
end
