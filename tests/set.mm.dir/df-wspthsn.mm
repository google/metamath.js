
axiom df-wspthsn
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  assert |- WSPathsN = ( n e. NN0 , g e. _V |-> { w e. ( n WWalksN g ) | E. f f ( SPaths ` g ) w } )
end
