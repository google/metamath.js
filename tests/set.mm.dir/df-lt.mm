
axiom df-lt
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- <RR = { <. x , y >. | ( ( x e. RR /\ y e. RR ) /\ E. z E. w ( ( x = <. z , 0R >. /\ y = <. w , 0R >. ) /\ z <R w ) ) }
end
