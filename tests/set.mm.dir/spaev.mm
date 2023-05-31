include "weq.mm"
include "equequ1.mm"
include "spw.mm"

theorem spaev
  param vx: setvar x
  param vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( A. x x = y -> x = y )

  proof
    vx
    vy
    weq
    vz
    vy
    weq
    vx
    vz
    vx
    vz
    vy
    equequ1
    spw
end
