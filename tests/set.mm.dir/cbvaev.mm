include "weq.mm"
include "wal.mm"
include "ax7.mm"
include "cbvalivw.mm"
include "syl.mm"

theorem cbvaev
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  let vt: setvar t

  disjoint x y
  disjoint y z
  disjoint t x
  disjoint t y
  disjoint t z
  assert |- ( A. x x = y -> A. z z = y )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    vt
    vy
    weq
    #
    vt
    wal
    vz
    vy
    weq
    #
    vz
    wal
    @0
    @1
    vx
    vt
    vx
    vt
    vy
    ax7
    cbvalivw
    @1
    @2
    vt
    vz
    vt
    vz
    vy
    ax7
    cbvalivw
    syl
end
