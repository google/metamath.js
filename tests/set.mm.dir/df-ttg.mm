
axiom df-ttg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vi: setvar i
  let vk: setvar k
  assert |- toTG = ( w e. _V |-> [_ ( x e. ( Base ` w ) , y e. ( Base ` w ) |-> { z e. ( Base ` w ) | E. k e. ( 0 [,] 1 ) ( z ( -g ` w ) x ) = ( k ( .s ` w ) ( y ( -g ` w ) x ) ) } ) / i ]_ ( ( w sSet <. ( Itv ` ndx ) , i >. ) sSet <. ( LineG ` ndx ) , ( x e. ( Base ` w ) , y e. ( Base ` w ) |-> { z e. ( Base ` w ) | ( z e. ( x i y ) \/ x e. ( z i y ) \/ y e. ( x i z ) ) } ) >. ) )
end
