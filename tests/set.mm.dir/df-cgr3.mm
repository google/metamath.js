
axiom df-cgr3
  let ve: setvar e
  let vf: setvar f
  let vn: setvar n
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assert |- Cgr3 = { <. p , q >. | E. n e. NN E. a e. ( EE ` n ) E. b e. ( EE ` n ) E. c e. ( EE ` n ) E. d e. ( EE ` n ) E. e e. ( EE ` n ) E. f e. ( EE ` n ) ( p = <. a , <. b , c >. >. /\ q = <. d , <. e , f >. >. /\ ( <. a , b >. Cgr <. d , e >. /\ <. a , c >. Cgr <. d , f >. /\ <. b , c >. Cgr <. e , f >. ) ) }
end
