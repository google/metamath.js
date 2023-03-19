
axiom df-psgn
  let vx: setvar x
  let vw: setvar w
  let vs: setvar s
  let vp: setvar p
  let vd: setvar d
  assert |- pmSgn = ( d e. _V |-> ( x e. { p e. ( Base ` ( SymGrp ` d ) ) | dom ( p \ _I ) e. Fin } |-> ( iota s E. w e. Word ran ( pmTrsp ` d ) ( x = ( ( SymGrp ` d ) gsum w ) /\ s = ( -u 1 ^ ( # ` w ) ) ) ) ) )
end
