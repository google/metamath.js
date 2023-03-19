include "weq.mm"
include "wal.mm"
include "wel.mm"
include "wn.mm"
include "elirrv.mm"
include "elequ2.mm"
include "mtbii.mm"
include "sps.mm"
include "sp.mm"
include "nsyl.mm"

theorem nd3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> -. A. z x e. y )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    vx
    vy
    wel
    #
    @1
    vz
    wal
    @0
    @1
    wn
    vx
    @0
    vx
    vx
    wel
    @1
    vx
    elirrv
    vx
    vy
    vx
    elequ2
    mtbii
    sps
    @1
    vz
    sp
    nsyl
end
