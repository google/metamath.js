
axiom df-perpg
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let vg: setvar g
  let va: setvar a
  let vb: setvar b
  assert |- perpG = ( g e. _V |-> { <. a , b >. | ( ( a e. ran ( LineG ` g ) /\ b e. ran ( LineG ` g ) ) /\ E. x e. ( a i^i b ) A. u e. a A. v e. b <" u x v "> e. ( raG ` g ) ) } )
end
