
axiom df-drng
  let vr: setvar r
  assert |- DivRing = { r e. Ring | ( Unit ` r ) = ( ( Base ` r ) \ { ( 0g ` r ) } ) }
end
