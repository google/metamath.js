include "weq.mm"
include "wal.mm"
include "spaev.mm"
include "alrimiv.mm"
include "cbvaev.mm"
include "equeuclr.mm"
include "al2imi.mm"
include "sylc.mm"

theorem aevlem0
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( A. x x = y -> A. z z = x )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    @0
    vz
    wal
    vz
    vy
    weq
    #
    vz
    wal
    vz
    vx
    weq
    #
    vz
    wal
    @1
    @0
    vz
    vx
    vy
    spaev
    alrimiv
    vx
    vy
    vz
    cbvaev
    @0
    @2
    @3
    vz
    vx
    vz
    vy
    equeuclr
    al2imi
    sylc
end
