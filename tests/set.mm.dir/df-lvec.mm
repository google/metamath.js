
axiom df-lvec
  let vf: setvar f
  assert |- LVec = { f e. LMod | ( Scalar ` f ) e. DivRing }
end
