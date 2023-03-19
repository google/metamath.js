
axiom df-xdiv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- /e = ( x e. RR* , y e. ( RR \ { 0 } ) |-> ( iota_ z e. RR* ( y *e z ) = x ) )
end
