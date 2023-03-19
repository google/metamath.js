
axiom df-arw
  let vc: setvar c
  assert |- Arrow = ( c e. Cat |-> U. ran ( HomA ` c ) )
end
