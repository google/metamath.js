include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "wsb.mm"
include "weu.mm"
include "nfv.mm"
include "sb8.mm"
include "equsb3.mm"
include "sblbis.mm"
include "albii.mm"
include "nfsb.mm"
include "nfbi.mm"
include "sbequ.mm"
include "equequ1.mm"
include "bibi12d.mm"
include "cbval.mm"
include "3bitri.mm"
include "exbii.mm"
include "df-eu.mm"
include "3bitr4i.mm"

theorem sb8eu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  assume sb8eu.1: |- F/ y ph


  assert |- ( E! x ph <-> E! y [ y / x ] ph )

  proof
    wph
    vx
    vz
    weq
    #
    wb
    #
    vx
    wal
    #
    vz
    wex
    wph
    vx
    vy
    wsb
    #
    vy
    vz
    weq
    #
    wb
    #
    vy
    wal
    #
    vz
    wex
    wph
    vx
    weu
    @3
    vy
    weu
    @2
    @6
    vz
    @2
    @1
    vx
    vw
    wsb
    #
    vw
    wal
    wph
    vx
    vw
    wsb
    #
    vw
    vz
    weq
    #
    wb
    #
    vw
    wal
    @6
    @1
    vx
    vw
    @1
    vw
    nfv
    sb8
    @7
    @10
    vw
    @0
    @9
    wph
    vx
    vw
    vw
    vx
    vz
    equsb3
    sblbis
    albii
    @10
    @5
    vw
    vy
    @8
    @9
    vy
    wph
    vx
    vw
    vy
    sb8eu.1
    nfsb
    @9
    vy
    nfv
    nfbi
    @5
    vw
    nfv
    vw
    vy
    weq
    @8
    @3
    @9
    @4
    wph
    vw
    vy
    vx
    sbequ
    vw
    vy
    vz
    equequ1
    bibi12d
    cbval
    3bitri
    exbii
    wph
    vx
    vz
    df-eu
    @3
    vy
    vz
    df-eu
    3bitr4i
end
