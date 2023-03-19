
axiom df-omn
  let vx: setvar x
  let vy: setvar y
  let vj: setvar j
  let vp: setvar p
  assert |- OmN = ( j e. Top , y e. U. j |-> seq 0 ( ( ( x e. _V , p e. _V |-> <. ( ( TopOpen ` ( 1st ` x ) ) Om1 ( 2nd ` x ) ) , ( ( 0 [,] 1 ) X. { ( 2nd ` x ) } ) >. ) o. 1st ) , <. { <. ( Base ` ndx ) , U. j >. , <. ( TopSet ` ndx ) , j >. } , y >. ) )
end
