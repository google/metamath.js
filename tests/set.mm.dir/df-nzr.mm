
axiom df-nzr
  let vr: setvar r
  assert |- NzRing = { r e. Ring | ( 1r ` r ) =/= ( 0g ` r ) }
end
