
axiom df-bigo
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  assert |- _O = ( g e. ( RR ^pm RR ) |-> { f e. ( RR ^pm RR ) | E. x e. RR E. m e. RR A. y e. ( dom f i^i ( x [,) +oo ) ) ( f ` y ) <_ ( m x. ( g ` y ) ) } )
end
