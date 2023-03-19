
axiom df-oexp
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- ^o = ( x e. On , y e. On |-> if ( x = (/) , ( 1o \ y ) , ( rec ( ( z e. _V |-> ( z .o x ) ) , 1o ) ` y ) ) )
end
