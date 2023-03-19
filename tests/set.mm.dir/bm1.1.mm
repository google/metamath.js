include "wel.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wex.mm"
include "weu.mm"
include "biantr.mm"
include "alanimi.mm"
include "ax-ext.mm"
include "syl.mm"
include "gen2.mm"
include "wmo.mm"
include "nfv.mm"
include "nfbi.mm"
include "nfal.mm"
include "elequ2.mm"
include "bibi1d.mm"
include "albidv.mm"
include "mo4f.mm"
include "df-mo.mm"
include "bitr3i.mm"
include "mpbi.mm"

theorem bm1.1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume bm1.1.1: |- F/ x ph

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( E. x A. y ( y e. x <-> ph ) -> E! x A. y ( y e. x <-> ph ) )

  proof
    vy
    vx
    wel
    #
    wph
    wb
    #
    vy
    wal
    #
    vy
    vz
    wel
    #
    wph
    wb
    #
    vy
    wal
    #
    wa
    #
    vx
    vz
    weq
    #
    wi
    #
    vz
    wal
    vx
    wal
    #
    @2
    vx
    wex
    @2
    vx
    weu
    wi
    #
    @8
    vx
    vz
    @6
    @0
    @3
    wb
    #
    vy
    wal
    @7
    @1
    @4
    @11
    vy
    @0
    wph
    @3
    biantr
    alanimi
    vx
    vz
    vy
    ax-ext
    syl
    gen2
    @9
    @2
    vx
    wmo
    @10
    @2
    @5
    vx
    vz
    @4
    vx
    vy
    @3
    wph
    vx
    @3
    vx
    nfv
    bm1.1.1
    nfbi
    nfal
    @7
    @1
    @4
    vy
    @7
    @0
    @3
    wph
    vx
    vz
    vy
    elequ2
    bibi1d
    albidv
    mo4f
    @2
    vx
    df-mo
    bitr3i
    mpbi
end
