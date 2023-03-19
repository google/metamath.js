
axiom df-vdwpc
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let va: setvar a
  let vd: setvar d
  assert |- PolyAP = { <. <. m , k >. , f >. | E. a e. NN E. d e. ( NN ^m ( 1 ... m ) ) ( A. i e. ( 1 ... m ) ( ( a + ( d ` i ) ) ( AP ` k ) ( d ` i ) ) C_ ( `' f " { ( f ` ( a + ( d ` i ) ) ) } ) /\ ( # ` ran ( i e. ( 1 ... m ) |-> ( f ` ( a + ( d ` i ) ) ) ) ) = m ) }
end
