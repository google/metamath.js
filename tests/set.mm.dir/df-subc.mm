
axiom df-subc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vc: setvar c
  assert |- Subcat = ( c e. Cat |-> { h | ( h C_cat ( Homf ` c ) /\ [. dom dom h / s ]. A. x e. s ( ( ( Id ` c ) ` x ) e. ( x h x ) /\ A. y e. s A. z e. s A. f e. ( x h y ) A. g e. ( y h z ) ( g ( <. x , y >. ( comp ` c ) z ) f ) e. ( x h z ) ) ) } )
end
