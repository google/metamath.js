
axiom df-dlat
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vb: setvar b
  assert |- DLat = { k e. Lat | [. ( Base ` k ) / b ]. [. ( join ` k ) / j ]. [. ( meet ` k ) / m ]. A. x e. b A. y e. b A. z e. b ( x m ( y j z ) ) = ( ( x m y ) j ( x m z ) ) }
end
