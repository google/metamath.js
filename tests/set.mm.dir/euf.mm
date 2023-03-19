include "weu.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "df-eu.mm"
include "nfv.mm"
include "nfbi.mm"
include "nfal.mm"
include "equequ2.mm"
include "bibi2d.mm"
include "albidv.mm"
include "cbvex.mm"
include "bitri.mm"

theorem euf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume euf.1: |- F/ y ph

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( E! x ph <-> E. y A. x ( ph <-> x = y ) )

  proof
    wph
    vx
    weu
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
    weq
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    wph
    vx
    vz
    df-eu
    @2
    @5
    vz
    vy
    @1
    vy
    vx
    wph
    @0
    vy
    euf.1
    @0
    vy
    nfv
    nfbi
    nfal
    @5
    vz
    nfv
    vz
    vy
    weq
    #
    @1
    @4
    vx
    @6
    @0
    @3
    wph
    vz
    vy
    vx
    equequ2
    bibi2d
    albidv
    cbvex
    bitri
end
