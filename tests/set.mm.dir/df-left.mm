
axiom df-left
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- _L = ( x e. No |-> { y e. ( _Old ` ( bday ` x ) ) | A. z e. No ( ( y <s z /\ z <s x ) -> ( bday ` y ) e. ( bday ` z ) ) } )
end
