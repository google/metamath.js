
axiom df-1stf
  let vx: setvar x
  let vy: setvar y
  let vs: setvar s
  let vr: setvar r
  let vb: setvar b
  assert |- 1stF = ( r e. Cat , s e. Cat |-> [_ ( ( Base ` r ) X. ( Base ` s ) ) / b ]_ <. ( 1st |` b ) , ( x e. b , y e. b |-> ( 1st |` ( x ( Hom ` ( r Xc. s ) ) y ) ) ) >. )
end
