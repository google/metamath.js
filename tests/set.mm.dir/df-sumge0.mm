
axiom df-sumge0
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  assert |- sum^ = ( x e. _V |-> if ( +oo e. ran x , +oo , sup ( ran ( y e. ( ~P dom x i^i Fin ) |-> sum_ w e. y ( x ` w ) ) , RR* , < ) ) )
end
