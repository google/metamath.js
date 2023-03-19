include "weq.mm"
include "wn.mm"
include "wel.mm"
include "wi.mm"
include "wex.mm"
include "wal.mm"
include "dtru.mm"
include "exnal.mm"
include "mpbir.mm"
include "pm2.21.mm"
include "eximii.mm"

theorem dvdemo1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  assert |- E. x ( x = y -> z e. x )

  proof
    vx
    vy
    weq
    #
    wn
    #
    @0
    vz
    vx
    wel
    #
    wi
    vx
    @1
    vx
    wex
    @0
    vx
    wal
    wn
    vx
    vy
    dtru
    @0
    vx
    exnal
    mpbir
    @0
    @2
    pm2.21
    eximii
end
