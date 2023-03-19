
axiom df-fae
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vr: setvar r
  assert |- ~ae = ( r e. _V , m e. U. ran measures |-> { <. f , g >. | ( ( f e. ( dom r ^m U. dom m ) /\ g e. ( dom r ^m U. dom m ) ) /\ { x e. U. dom m | ( f ` x ) r ( g ` x ) } ae m ) } )
end
