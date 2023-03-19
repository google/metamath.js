include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "coprab.mm"
include "nfv.mm"
include "nfan.mm"
include "nfex.mm"
include "opeq2.mm"
include "opeq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "cbvex.mm"
include "exbii.mm"
include "abbii.mm"
include "df-oprab.mm"
include "3eqtr4i.mm"

theorem cbvoprab2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assume cbvoprab2.1: |- F/ w ph
  assume cbvoprab2.2: |- F/ y ps
  assume cbvoprab2.3: |- ( y = w -> ( ph <-> ps ) )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint ps v
  assert |- { <. <. x , y >. , z >. | ph } = { <. <. x , w >. , z >. | ps }

  proof
    vv
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    vz
    cv
    #
    cop
    #
    wceq
    #
    wph
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
    vv
    cab
    @0
    @1
    vw
    cv
    #
    cop
    #
    @4
    cop
    #
    wceq
    #
    wps
    wa
    #
    vz
    wex
    #
    vw
    wex
    #
    vx
    wex
    #
    vv
    cab
    wph
    vx
    vy
    vz
    coprab
    wps
    vx
    vw
    vz
    coprab
    @10
    @18
    vv
    @9
    @17
    vx
    @8
    @16
    vy
    vw
    @7
    vw
    vz
    @6
    wph
    vw
    @6
    vw
    nfv
    cbvoprab2.1
    nfan
    nfex
    @15
    vy
    vz
    @14
    wps
    vy
    @14
    vy
    nfv
    cbvoprab2.2
    nfan
    nfex
    @2
    @11
    wceq
    #
    @7
    @15
    vz
    @19
    @6
    @14
    wph
    wps
    @19
    @5
    @13
    @0
    @19
    @3
    @12
    @4
    @2
    @11
    @1
    opeq2
    opeq1d
    eqeq2d
    cbvoprab2.3
    anbi12d
    exbidv
    cbvex
    exbii
    abbii
    wph
    vx
    vy
    vz
    vv
    df-oprab
    wps
    vx
    vw
    vz
    vv
    df-oprab
    3eqtr4i
end
