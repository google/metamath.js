
axiom df-right
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assert |- _R = ( x e. No |-> { y e. ( _Old ` ( bday ` x ) ) | A. z e. No ( ( x <s z /\ z <s y ) -> ( bday ` y ) e. ( bday ` z ) ) } )
end
