
axiom df-lss
  let vx: setvar x
  let vw: setvar w
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  assert |- LSubSp = ( w e. _V |-> { s e. ( ~P ( Base ` w ) \ { (/) } ) | A. x e. ( Base ` ( Scalar ` w ) ) A. a e. s A. b e. s ( ( x ( .s ` w ) a ) ( +g ` w ) b ) e. s } )
end
