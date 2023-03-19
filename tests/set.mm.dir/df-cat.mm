
axiom df-cat
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vo: setvar o
  let vb: setvar b
  let vc: setvar c
  assert |- Cat = { c | [. ( Base ` c ) / b ]. [. ( Hom ` c ) / h ]. [. ( comp ` c ) / o ]. A. x e. b ( E. g e. ( x h x ) A. y e. b ( A. f e. ( y h x ) ( g ( <. y , x >. o x ) f ) = f /\ A. f e. ( x h y ) ( f ( <. x , x >. o y ) g ) = f ) /\ A. y e. b A. z e. b A. f e. ( x h y ) A. g e. ( y h z ) ( ( g ( <. x , y >. o z ) f ) e. ( x h z ) /\ A. w e. b A. k e. ( z h w ) ( ( k ( <. y , z >. o w ) g ) ( <. x , y >. o w ) f ) = ( k ( <. x , z >. o w ) ( g ( <. x , y >. o z ) f ) ) ) ) }
end
