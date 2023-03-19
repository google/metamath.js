include "weq.mm"
include "wal.mm"
include "axc11n.mm"
include "impbii.mm"

theorem aecom
  param vx: setvar x
  param vy: setvar y


  assert |- ( A. x x = y <-> A. y y = x )

  proof
    vx
    vy
    weq
    vx
    wal
    vy
    vx
    weq
    vy
    wal
    vx
    vy
    axc11n
    vy
    vx
    axc11n
    impbii
end
