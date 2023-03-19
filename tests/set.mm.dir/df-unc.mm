
axiom df-unc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  assert |- uncurry F = { <. <. x , y >. , z >. | y ( F ` x ) z }
end
