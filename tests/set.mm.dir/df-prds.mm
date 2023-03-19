
axiom df-prds
  let vx: setvar x
  let vv: setvar v
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  assert |- Xs_ = ( s e. _V , r e. _V |-> [_ X_ x e. dom r ( Base ` ( r ` x ) ) / v ]_ [_ ( f e. v , g e. v |-> X_ x e. dom r ( ( f ` x ) ( Hom ` ( r ` x ) ) ( g ` x ) ) ) / h ]_ ( ( { <. ( Base ` ndx ) , v >. , <. ( +g ` ndx ) , ( f e. v , g e. v |-> ( x e. dom r |-> ( ( f ` x ) ( +g ` ( r ` x ) ) ( g ` x ) ) ) ) >. , <. ( .r ` ndx ) , ( f e. v , g e. v |-> ( x e. dom r |-> ( ( f ` x ) ( .r ` ( r ` x ) ) ( g ` x ) ) ) ) >. } u. { <. ( Scalar ` ndx ) , s >. , <. ( .s ` ndx ) , ( f e. ( Base ` s ) , g e. v |-> ( x e. dom r |-> ( f ( .s ` ( r ` x ) ) ( g ` x ) ) ) ) >. , <. ( .i ` ndx ) , ( f e. v , g e. v |-> ( s gsum ( x e. dom r |-> ( ( f ` x ) ( .i ` ( r ` x ) ) ( g ` x ) ) ) ) ) >. } ) u. ( { <. ( TopSet ` ndx ) , ( Xt_ ` ( TopOpen o. r ) ) >. , <. ( le ` ndx ) , { <. f , g >. | ( { f , g } C_ v /\ A. x e. dom r ( f ` x ) ( le ` ( r ` x ) ) ( g ` x ) ) } >. , <. ( dist ` ndx ) , ( f e. v , g e. v |-> sup ( ( ran ( x e. dom r |-> ( ( f ` x ) ( dist ` ( r ` x ) ) ( g ` x ) ) ) u. { 0 } ) , RR* , < ) ) >. } u. { <. ( Hom ` ndx ) , h >. , <. ( comp ` ndx ) , ( a e. ( v X. v ) , c e. v |-> ( d e. ( c h ( 2nd ` a ) ) , e e. ( h ` a ) |-> ( x e. dom r |-> ( ( d ` x ) ( <. ( ( 1st ` a ) ` x ) , ( ( 2nd ` a ) ` x ) >. ( comp ` ( r ` x ) ) ( c ` x ) ) ( e ` x ) ) ) ) ) >. } ) ) )
end
