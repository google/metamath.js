include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "coprab.mm"
include "nfv.mm"
include "nfan.mm"
include "nfex.mm"
include "anbi2d.mm"
include "2exbidv.mm"
include "cbvopab2.mm"
include "dfoprab2.mm"
include "3eqtr4i.mm"

theorem cbvoprab3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assume cbvoprab3.1: |- F/ w ph
  assume cbvoprab3.2: |- F/ z ps
  assume cbvoprab3.3: |- ( z = w -> ( ph <-> ps ) )

  disjoint x z
  disjoint w x
  disjoint w z
  disjoint y z
  disjoint w y
  disjoint v x
  disjoint v z
  disjoint v w
  disjoint v y
  disjoint ph v
  disjoint ps v
  assert |- { <. <. x , y >. , z >. | ph } = { <. <. x , y >. , w >. | ps }

  proof
    vv
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
    #
    vx
    wex
    #
    vv
    vz
    copab
    @0
    wps
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    vv
    vw
    copab
    wph
    vx
    vy
    vz
    coprab
    wps
    vx
    vy
    vw
    coprab
    @3
    @6
    vv
    vz
    vw
    @2
    vw
    vx
    @1
    vw
    vy
    @0
    wph
    vw
    @0
    vw
    nfv
    cbvoprab3.1
    nfan
    nfex
    nfex
    @5
    vz
    vx
    @4
    vz
    vy
    @0
    wps
    vz
    @0
    vz
    nfv
    cbvoprab3.2
    nfan
    nfex
    nfex
    vz
    cv
    vw
    cv
    wceq
    #
    @1
    @4
    vx
    vy
    @7
    wph
    wps
    @0
    cbvoprab3.3
    anbi2d
    2exbidv
    cbvopab2
    wph
    vx
    vy
    vz
    vv
    dfoprab2
    wps
    vx
    vy
    vw
    vv
    dfoprab2
    3eqtr4i
end
