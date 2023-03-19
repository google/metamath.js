
axiom df-vol
  let vx: setvar x
  let vy: setvar y
  assert |- vol = ( vol* |` { x | A. y e. ( `' vol* " RR ) ( vol* ` y ) = ( ( vol* ` ( y i^i x ) ) + ( vol* ` ( y \ x ) ) ) } )
end
