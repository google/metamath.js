
axiom df-topsp
  let vf: setvar f
  assert |- TopSp = { f | ( TopOpen ` f ) e. ( TopOn ` ( Base ` f ) ) }
end
