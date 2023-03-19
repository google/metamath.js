include "coprab.mm"
include "cdm.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "cab.mm"
include "dfoprab2.mm"
include "dmeqi.mm"
include "dmopab.mm"
include "exrot3.mm"
include "19.42v.mm"
include "2exbii.mm"
include "bitri.mm"
include "abbii.mm"
include "df-opab.mm"
include "eqtr4i.mm"
include "3eqtri.mm"

theorem dmoprab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w z
  disjoint w y
  disjoint ph w
  assert |- dom { <. <. x , y >. , z >. | ph } = { <. x , y >. | E. z ph }

  proof
    wph
    vx
    vy
    vz
    coprab
    #
    cdm
    vw
    cv
    vx
    cv
    vy
    cv
    cop
    wceq
    #
    wph
    wa
    #
    vy
    wex
    vx
    wex
    #
    vw
    vz
    copab
    #
    cdm
    @3
    vz
    wex
    #
    vw
    cab
    #
    wph
    vz
    wex
    #
    vx
    vy
    copab
    #
    @0
    @4
    wph
    vx
    vy
    vz
    vw
    dfoprab2
    dmeqi
    @3
    vw
    vz
    dmopab
    @6
    @1
    @7
    wa
    #
    vy
    wex
    vx
    wex
    #
    vw
    cab
    @8
    @5
    @10
    vw
    @5
    @2
    vz
    wex
    #
    vy
    wex
    vx
    wex
    @10
    @2
    vz
    vx
    vy
    exrot3
    @11
    @9
    vx
    vy
    @1
    wph
    vz
    19.42v
    2exbii
    bitri
    abbii
    @7
    vx
    vy
    vw
    df-opab
    eqtr4i
    3eqtri
end
