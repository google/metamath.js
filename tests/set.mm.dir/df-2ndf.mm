
axiom df-2ndf
  let vx: setvar x
  let vy: setvar y
  let vs: setvar s
  let vr: setvar r
  let vb: setvar b
  assert |- 2ndF = ( r e. Cat , s e. Cat |-> [_ ( ( Base ` r ) X. ( Base ` s ) ) / b ]_ <. ( 2nd |` b ) , ( x e. b , y e. b |-> ( 2nd |` ( x ( Hom ` ( r Xc. s ) ) y ) ) ) >. )
end
