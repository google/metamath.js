
axiom df-enq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  assert |- ~Q = { <. x , y >. | ( ( x e. ( N. X. N. ) /\ y e. ( N. X. N. ) ) /\ E. z E. w E. v E. u ( ( x = <. z , w >. /\ y = <. v , u >. ) /\ ( z .N u ) = ( w .N v ) ) ) }
end
