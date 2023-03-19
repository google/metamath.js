
axiom df-wspthsnon
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  assert |- WSPathsNOn = ( n e. NN0 , g e. _V |-> ( a e. ( Vtx ` g ) , b e. ( Vtx ` g ) |-> { w e. ( a ( n WWalksNOn g ) b ) | E. f f ( a ( SPathsOn ` g ) b ) w } ) )
end
