
axiom df-cid
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vo: setvar o
  let vb: setvar b
  let vc: setvar c
  assert |- Id = ( c e. Cat |-> [_ ( Base ` c ) / b ]_ [_ ( Hom ` c ) / h ]_ [_ ( comp ` c ) / o ]_ ( x e. b |-> ( iota_ g e. ( x h x ) A. y e. b ( A. f e. ( y h x ) ( g ( <. y , x >. o x ) f ) = f /\ A. f e. ( x h y ) ( f ( <. x , x >. o y ) g ) = f ) ) ) )
end
