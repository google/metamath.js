include "weq.mm"
include "wel.mm"
include "wb.mm"
include "wal.mm"
include "bj-elequ2g.mm"
include "axext3.mm"
include "impbii.mm"

theorem bj-cleqhyp
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  disjoint y z
  assert |- ( x = y <-> A. z ( z e. x <-> z e. y ) )

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
    wal
    vx
    vy
    vz
    bj-elequ2g
    vx
    vy
    vz
    axext3
    impbii
end
