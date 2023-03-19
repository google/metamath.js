
axiom df-homlimb
  let vx: setvar x
  let vv: setvar v
  let ve: setvar e
  let vf: setvar f
  let vn: setvar n
  let vs: setvar s
  assert |- HomLimB = ( f e. _V |-> [_ U_ n e. NN ( { n } X. dom ( f ` n ) ) / v ]_ [_ |^| { s | ( s Er v /\ ( x e. v |-> <. ( ( 1st ` x ) + 1 ) , ( ( f ` ( 1st ` x ) ) ` ( 2nd ` x ) ) >. ) C_ s ) } / e ]_ <. ( v /. e ) , ( n e. NN |-> ( x e. dom ( f ` n ) |-> [ <. n , x >. ] e ) ) >. )
end
