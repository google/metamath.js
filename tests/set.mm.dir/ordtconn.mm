include "tru.mm"

theorem ordtconn
  let cB: class B
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  assume ordtconn.x: |- B = ( Base ` K )
  assume ordtconn.l: |- .<_ = ( ( le ` K ) i^i ( B X. B ) )
  assume ordtconn.j: |- J = ( ordTop ` .<_ )


  assert |- T.

  proof
    tru
end
