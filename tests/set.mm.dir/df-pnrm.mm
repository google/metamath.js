
axiom df-pnrm
  let vf: setvar f
  let vj: setvar j
  assert |- PNrm = { j e. Nrm | ( Clsd ` j ) C_ ran ( f e. ( j ^m NN ) |-> |^| ran f ) }
end
