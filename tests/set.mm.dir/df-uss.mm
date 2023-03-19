
axiom df-uss
  let vf: setvar f
  assert |- UnifSt = ( f e. _V |-> ( ( UnifSet ` f ) |`t ( ( Base ` f ) X. ( Base ` f ) ) ) )
end
