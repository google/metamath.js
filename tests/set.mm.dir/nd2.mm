include "weq.mm"
include "wal.mm"
include "wel.mm"
include "elirrv.mm"
include "wsb.mm"
include "stdpc4.mm"
include "nfnth.mm"
include "elequ2.mm"
include "sbie.mm"
include "sylib.mm"
include "mto.mm"
include "axc11.mm"
include "mtoi.mm"

theorem nd2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> -. A. x z e. y )

  proof
    vx
    vy
    weq
    vx
    wal
    vz
    vy
    wel
    #
    vx
    wal
    @0
    vy
    wal
    #
    @1
    vz
    vz
    wel
    #
    vz
    elirrv
    #
    @1
    @0
    vy
    vz
    wsb
    @2
    @0
    vy
    vz
    stdpc4
    @0
    @2
    vy
    vz
    @2
    vy
    @3
    nfnth
    vy
    vz
    vz
    elequ2
    sbie
    sylib
    mto
    @0
    vx
    vy
    axc11
    mtoi
end
