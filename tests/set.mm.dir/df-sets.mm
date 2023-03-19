
axiom df-sets
  let ve: setvar e
  let vs: setvar s
  assert |- sSet = ( s e. _V , e e. _V |-> ( ( s |` ( _V \ dom { e } ) ) u. { e } ) )
end
