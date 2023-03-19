
axiom df-afs
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assert |- AFS = ( g e. TarskiG |-> { <. e , f >. | [. ( Base ` g ) / p ]. [. ( dist ` g ) / h ]. [. ( Itv ` g ) / i ]. E. a e. p E. b e. p E. c e. p E. d e. p E. x e. p E. y e. p E. z e. p E. w e. p ( e = <. <. a , b >. , <. c , d >. >. /\ f = <. <. x , y >. , <. z , w >. >. /\ ( ( b e. ( a i c ) /\ y e. ( x i z ) ) /\ ( ( a h b ) = ( x h y ) /\ ( b h c ) = ( y h z ) ) /\ ( ( a h d ) = ( x h w ) /\ ( b h d ) = ( y h w ) ) ) ) } )
end
