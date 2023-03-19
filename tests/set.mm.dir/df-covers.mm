
axiom df-covers
  let vz: setvar z
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assert |- <o = ( p e. _V |-> { <. a , b >. | ( ( a e. ( Base ` p ) /\ b e. ( Base ` p ) ) /\ a ( lt ` p ) b /\ -. E. z e. ( Base ` p ) ( a ( lt ` p ) z /\ z ( lt ` p ) b ) ) } )
end
