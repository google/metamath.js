include "weq.mm"
include "weu.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "ax6evr.mm"
include "equequ2.mm"
include "alrimiv.mm"
include "eximii.mm"
include "df-eu.mm"
include "mpbir.mm"

theorem euequ1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- E! x x = y

  proof
    vx
    vy
    weq
    #
    vx
    weu
    @0
    vx
    vz
    weq
    wb
    #
    vx
    wal
    #
    vz
    wex
    vy
    vz
    weq
    #
    @2
    vz
    vz
    vy
    ax6evr
    @3
    @1
    vx
    vy
    vz
    vx
    equequ2
    alrimiv
    eximii
    @0
    vx
    vz
    df-eu
    mpbir
end
