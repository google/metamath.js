
axiom df-ind
  let vx: setvar x
  let vo: setvar o
  let va: setvar a
  assert |- _Ind = ( o e. _V |-> ( a e. ~P o |-> ( x e. o |-> if ( x e. a , 1 , 0 ) ) ) )
end
