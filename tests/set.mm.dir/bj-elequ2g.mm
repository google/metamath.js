include "weq.mm"
include "wel.mm"
include "wb.mm"
include "elequ2.mm"
include "alrimiv.mm"

theorem bj-elequ2g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  disjoint y z
  assert |- ( x = y -> A. z ( z e. x <-> z e. y ) )

  proof
    vx
    vy
    weq
    vz
    vx
    wel
    vz
    vy
    wel
    wb
    vz
    vx
    vy
    vz
    elequ2
    alrimiv
end
