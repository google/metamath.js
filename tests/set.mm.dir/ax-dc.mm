
axiom ax-dc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vn: setvar n
  assert |- ( ( E. y E. z y x z /\ ran x C_ dom x ) -> E. f A. n e. _om ( f ` n ) x ( f ` suc n ) )
end
