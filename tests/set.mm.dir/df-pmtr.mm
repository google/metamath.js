
axiom df-pmtr
  let vy: setvar y
  let vz: setvar z
  let vp: setvar p
  let vd: setvar d
  assert |- pmTrsp = ( d e. _V |-> ( p e. { y e. ~P d | y ~~ 2o } |-> ( z e. d |-> if ( z e. p , U. ( p \ { z } ) , z ) ) ) )
end
