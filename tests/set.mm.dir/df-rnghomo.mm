
axiom df-rnghomo
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f
  let vs: setvar s
  let vr: setvar r
  assert |- RngHomo = ( r e. Rng , s e. Rng |-> [_ ( Base ` r ) / v ]_ [_ ( Base ` s ) / w ]_ { f e. ( w ^m v ) | A. x e. v A. y e. v ( ( f ` ( x ( +g ` r ) y ) ) = ( ( f ` x ) ( +g ` s ) ( f ` y ) ) /\ ( f ` ( x ( .r ` r ) y ) ) = ( ( f ` x ) ( .r ` s ) ( f ` y ) ) ) } )
end
