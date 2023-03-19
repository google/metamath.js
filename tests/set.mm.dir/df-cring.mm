
axiom df-cring
  let vf: setvar f
  assert |- CRing = { f e. Ring | ( mulGrp ` f ) e. CMnd }
end
