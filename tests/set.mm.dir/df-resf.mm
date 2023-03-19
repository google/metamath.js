
axiom df-resf
  let vx: setvar x
  let vf: setvar f
  let vh: setvar h
  assert |- |`f = ( f e. _V , h e. _V |-> <. ( ( 1st ` f ) |` dom dom h ) , ( x e. dom h |-> ( ( ( 2nd ` f ) ` x ) |` ( h ` x ) ) ) >. )
end
