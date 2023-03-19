
axiom df-ltr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  assert |- <R = { <. x , y >. | ( ( x e. R. /\ y e. R. ) /\ E. z E. w E. v E. u ( ( x = [ <. z , w >. ] ~R /\ y = [ <. v , u >. ] ~R ) /\ ( z +P. u ) <P ( w +P. v ) ) ) }
end
