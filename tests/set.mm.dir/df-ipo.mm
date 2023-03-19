
axiom df-ipo
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vo: setvar o
  assert |- toInc = ( f e. _V |-> [_ { <. x , y >. | ( { x , y } C_ f /\ x C_ y ) } / o ]_ ( { <. ( Base ` ndx ) , f >. , <. ( TopSet ` ndx ) , ( ordTop ` o ) >. } u. { <. ( le ` ndx ) , o >. , <. ( oc ` ndx ) , ( x e. f |-> U. { y e. f | ( y i^i x ) = (/) } ) >. } ) )
end
