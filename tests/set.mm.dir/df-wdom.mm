
axiom df-wdom
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- ~<_* = { <. x , y >. | ( x = (/) \/ E. z z : y -onto-> x ) }
end
