
axiom df-pm2mp
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vq: setvar q
  let va: setvar a
  assert |- pMatToMatPoly = ( n e. Fin , r e. _V |-> ( m e. ( Base ` ( n Mat ( Poly1 ` r ) ) ) |-> [_ ( n Mat r ) / a ]_ [_ ( Poly1 ` a ) / q ]_ ( q gsum ( k e. NN0 |-> ( ( m decompPMat k ) ( .s ` q ) ( k ( .g ` ( mulGrp ` q ) ) ( var1 ` a ) ) ) ) ) ) )
end
