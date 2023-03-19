include "weq.mm"
include "wal.mm"
include "bj-hbaeb2.mm"
include "alcom.mm"
include "bitri.mm"

theorem bj-hbaeb
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y <-> A. z A. x x = y )

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
    vx
    wal
    @1
    vz
    wal
    vx
    vy
    vz
    bj-hbaeb2
    @0
    vx
    vz
    alcom
    bitri
end
