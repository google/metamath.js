
axiom df-tgp
  let vf: setvar f
  let vj: setvar j
  assert |- TopGrp = { f e. ( Grp i^i TopMnd ) | [. ( TopOpen ` f ) / j ]. ( invg ` f ) e. ( j Cn j ) }
end
