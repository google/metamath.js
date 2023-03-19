include "weq.mm"
include "wal.mm"
include "ax7.mm"
include "al2imi.mm"
include "axc11.mm"
include "syld.mm"

theorem wl-aetr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> ( A. x x = z -> A. y y = z ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    vx
    vz
    weq
    #
    vx
    wal
    vy
    vz
    weq
    #
    vx
    wal
    @2
    vy
    wal
    @0
    @1
    @2
    vx
    vx
    vy
    vz
    ax7
    al2imi
    @2
    vx
    vy
    axc11
    syld
end
