
axiom df-domn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vr: setvar r
  let vb: setvar b
  assert |- Domn = { r e. NzRing | [. ( Base ` r ) / b ]. [. ( 0g ` r ) / z ]. A. x e. b A. y e. b ( ( x ( .r ` r ) y ) = z -> ( x = z \/ y = z ) ) }
end
