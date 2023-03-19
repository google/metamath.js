
axiom df-homlim
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let vs: setvar s
  let vr: setvar r
  assert |- HomLim = ( r e. _V , f e. _V |-> [_ ( HomLimB ` f ) / e ]_ [_ ( 1st ` e ) / v ]_ [_ ( 2nd ` e ) / g ]_ ( { <. ( Base ` ndx ) , v >. , <. ( +g ` ndx ) , U_ n e. NN ran ( x e. dom ( g ` n ) , y e. dom ( g ` n ) |-> <. <. ( ( g ` n ) ` x ) , ( ( g ` n ) ` y ) >. , ( ( g ` n ) ` ( x ( +g ` ( r ` n ) ) y ) ) >. ) >. , <. ( .r ` ndx ) , U_ n e. NN ran ( x e. dom ( g ` n ) , y e. dom ( g ` n ) |-> <. <. ( ( g ` n ) ` x ) , ( ( g ` n ) ` y ) >. , ( ( g ` n ) ` ( x ( .r ` ( r ` n ) ) y ) ) >. ) >. } u. { <. ( TopOpen ` ndx ) , { s e. ~P v | A. n e. NN ( `' ( g ` n ) " s ) e. ( TopOpen ` ( r ` n ) ) } >. , <. ( dist ` ndx ) , U_ n e. NN ran ( x e. dom ( ( g ` n ) ` n ) , y e. dom ( ( g ` n ) ` n ) |-> <. <. ( ( g ` n ) ` x ) , ( ( g ` n ) ` y ) >. , ( x ( dist ` ( r ` n ) ) y ) >. ) >. , <. ( le ` ndx ) , U_ n e. NN ( `' ( g ` n ) o. ( ( le ` ( r ` n ) ) o. ( g ` n ) ) ) >. } ) )
end
