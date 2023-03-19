
axiom df-enr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  assert |- ~R = { <. x , y >. | ( ( x e. ( P. X. P. ) /\ y e. ( P. X. P. ) ) /\ E. z E. w E. v E. u ( ( x = <. z , w >. /\ y = <. v , u >. ) /\ ( z +P. u ) = ( w +P. v ) ) ) }
end
