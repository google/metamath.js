include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "copab.mm"
include "anbi2d.mm"
include "exbid.mm"
include "abbidv.mm"
include "df-opab.mm"
include "3eqtr4g.mm"

theorem opabbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume opabbid.1: |- F/ x ph
  assume opabbid.2: |- F/ y ph
  assume opabbid.3: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> { <. x , y >. | ps } = { <. x , y >. | ch } )

  proof
    wph
    vz
    cv
    vx
    cv
    vy
    cv
    cop
    wceq
    #
    wps
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    vz
    cab
    @0
    wch
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    vz
    cab
    wps
    vx
    vy
    copab
    wch
    vx
    vy
    copab
    wph
    @3
    @6
    vz
    wph
    @2
    @5
    vx
    opabbid.1
    wph
    @1
    @4
    vy
    opabbid.2
    wph
    wps
    wch
    @0
    opabbid.3
    anbi2d
    exbid
    exbid
    abbidv
    wps
    vx
    vy
    vz
    df-opab
    wch
    vx
    vy
    vz
    df-opab
    3eqtr4g
end
