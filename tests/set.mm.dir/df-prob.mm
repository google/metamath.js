
axiom df-prob
  let vp: setvar p
  assert |- Prob = { p e. U. ran measures | ( p ` U. dom p ) = 1 }
end
