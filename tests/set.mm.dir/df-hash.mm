
axiom df-hash
  let vx: setvar x
  assert |- # = ( ( ( rec ( ( x e. _V |-> ( x + 1 ) ) , 0 ) |` _om ) o. card ) u. ( ( _V \ Fin ) X. { +oo } ) )
end
