include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wb.mm"
include "wex.mm"
include "weu.mm"
include "ax6ev.mm"
include "nfv.mm"
include "nfnae.mm"
include "nfeqf2.mm"
include "wi.mm"
include "equequ2.mm"
include "equcoms.mm"
include "a1i.mm"
include "alrimdd.mm"
include "eximd.mm"
include "mpi.mm"
include "df-eu.mm"
include "sylibr.mm"

theorem wl-euequ1f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -. A. x x = y -> E! x x = y )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
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
    #
    @0
    vx
    weu
    @1
    vz
    vy
    weq
    #
    vz
    wex
    @4
    vz
    vy
    ax6ev
    @1
    @5
    @3
    vz
    @1
    vz
    nfv
    @1
    @5
    @2
    vx
    vx
    vy
    vx
    nfnae
    vx
    vy
    vz
    nfeqf2
    @5
    @2
    wi
    @1
    @2
    vy
    vz
    vy
    vz
    vx
    equequ2
    equcoms
    a1i
    alrimdd
    eximd
    mpi
    @0
    vx
    vz
    df-eu
    sylibr
end
