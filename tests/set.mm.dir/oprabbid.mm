include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "coprab.mm"
include "anbi2d.mm"
include "exbid.mm"
include "abbidv.mm"
include "df-oprab.mm"
include "3eqtr4g.mm"

theorem oprabbid
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume oprabbid.1: |- F/ x ph
  assume oprabbid.2: |- F/ y ph
  assume oprabbid.3: |- F/ z ph
  assume oprabbid.4: |- ( ph -> ( ps <-> ch ) )

  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w z
  disjoint w y
  disjoint ph w
  disjoint ps w
  disjoint ch w
  assert |- ( ph -> { <. <. x , y >. , z >. | ps } = { <. <. x , y >. , z >. | ch } )

  proof
    wph
    vw
    cv
    vx
    cv
    vy
    cv
    cop
    vz
    cv
    cop
    wceq
    #
    wps
    wa
    #
    vz
    wex
    #
    vy
    wex
    #
    vx
    wex
    #
    vw
    cab
    @0
    wch
    wa
    #
    vz
    wex
    #
    vy
    wex
    #
    vx
    wex
    #
    vw
    cab
    wps
    vx
    vy
    vz
    coprab
    wch
    vx
    vy
    vz
    coprab
    wph
    @4
    @8
    vw
    wph
    @3
    @7
    vx
    oprabbid.1
    wph
    @2
    @6
    vy
    oprabbid.2
    wph
    @1
    @5
    vz
    oprabbid.3
    wph
    wps
    wch
    @0
    oprabbid.4
    anbi2d
    exbid
    exbid
    exbid
    abbidv
    wps
    vx
    vy
    vz
    vw
    df-oprab
    wch
    vx
    vy
    vz
    vw
    df-oprab
    3eqtr4g
end
