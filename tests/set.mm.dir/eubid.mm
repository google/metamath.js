include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "weu.mm"
include "bibi1d.mm"
include "albid.mm"
include "exbidv.mm"
include "df-eu.mm"
include "3bitr4g.mm"

theorem eubid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume eubid.1: |- F/ x ph
  assume eubid.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( E! x ps <-> E! x ch ) )

  proof
    wph
    wps
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
    wch
    @0
    wb
    #
    vx
    wal
    #
    vy
    wex
    wps
    vx
    weu
    wch
    vx
    weu
    wph
    @2
    @4
    vy
    wph
    @1
    @3
    vx
    eubid.1
    wph
    wps
    wch
    @0
    eubid.2
    bibi1d
    albid
    exbidv
    wps
    vx
    vy
    df-eu
    wch
    vx
    vy
    df-eu
    3bitr4g
end
