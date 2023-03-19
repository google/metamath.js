
axiom df-leag
  let vx: setvar x
  let vg: setvar g
  let va: setvar a
  let vb: setvar b
  assert |- leA = ( g e. _V |-> { <. a , b >. | ( ( a e. ( ( Base ` g ) ^m ( 0 ..^ 3 ) ) /\ b e. ( ( Base ` g ) ^m ( 0 ..^ 3 ) ) ) /\ E. x e. ( Base ` g ) ( x ( inA ` g ) <" ( b ` 0 ) ( b ` 1 ) ( b ` 2 ) "> /\ <" ( a ` 0 ) ( a ` 1 ) ( a ` 2 ) "> ( cgrA ` g ) <" ( b ` 0 ) ( b ` 1 ) x "> ) ) } )
end
