
axiom df-usp
  let vf: setvar f
  assert |- UnifSp = { f | ( ( UnifSt ` f ) e. ( UnifOn ` ( Base ` f ) ) /\ ( TopOpen ` f ) = ( unifTop ` ( UnifSt ` f ) ) ) }
end
