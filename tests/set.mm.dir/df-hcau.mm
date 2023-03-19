
axiom df-hcau
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  assert |- Cauchy = { f e. ( ~H ^m NN ) | A. x e. RR+ E. y e. NN A. z e. ( ZZ>= ` y ) ( normh ` ( ( f ` y ) -h ( f ` z ) ) ) < x }
end
