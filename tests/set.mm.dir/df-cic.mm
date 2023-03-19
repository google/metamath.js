
axiom df-cic
  let vc: setvar c
  assert |- ~=c = ( c e. Cat |-> ( ( Iso ` c ) supp (/) ) )
end
