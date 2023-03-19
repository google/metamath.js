
axiom df-lpir
  let vw: setvar w
  assert |- LPIR = { w e. Ring | ( LIdeal ` w ) = ( LPIdeal ` w ) }
end
