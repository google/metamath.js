include "wex.mm"
include "weu.mm"
include "wi.mm"
include "wmo.mm"
include "exbid.mm"
include "eubid.mm"
include "imbi12d.mm"
include "df-mo.mm"
include "3bitr4g.mm"

theorem mobid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume mobid.1: |- F/ x ph
  assume mobid.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( E* x ps <-> E* x ch ) )

  proof
    wph
    wps
    vx
    wex
    #
    wps
    vx
    weu
    #
    wi
    wch
    vx
    wex
    #
    wch
    vx
    weu
    #
    wi
    wps
    vx
    wmo
    wch
    vx
    wmo
    wph
    @0
    @2
    @1
    @3
    wph
    wps
    wch
    vx
    mobid.1
    mobid.2
    exbid
    wph
    wps
    wch
    vx
    mobid.1
    mobid.2
    eubid
    imbi12d
    wps
    vx
    df-mo
    wch
    vx
    df-mo
    3bitr4g
end
