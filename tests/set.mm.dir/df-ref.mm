
axiom df-ref
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assert |- Ref = { <. x , y >. | ( U. y = U. x /\ A. z e. x E. w e. y z C_ w ) }
end
