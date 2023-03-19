
axiom df-cur
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  assert |- curry F = ( x e. dom dom F |-> { <. y , z >. | <. x , y >. F z } )
end
