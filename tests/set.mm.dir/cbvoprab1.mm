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
include "opeq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "cbvex.mm"
include "opabbii.mm"
include "dfoprab2.mm"
include "3eqtr4i.mm"

theorem cbvoprab1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assume cbvoprab1.1: |- F/ w ph
  assume cbvoprab1.2: |- F/ x ps
  assume cbvoprab1.3: |- ( x = w -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint v w
  disjoint ph v
  disjoint ps v
  assert |- { <. <. x , y >. , z >. | ph } = { <. <. w , y >. , z >. | ps }

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
    vw
    cv
    #
    @2
    cop
    #
    wceq
    #
    wps
    wa
    #
    vy
    wex
    #
    vw
    wex
    #
    vv
    vz
    copab
    wph
    vx
    vy
    vz
    coprab
    wps
    vw
    vy
    vz
    coprab
    @7
    @13
    vv
    vz
    @6
    @12
    vx
    vw
    @5
    vw
    vy
    @4
    wph
    vw
    @4
    vw
    nfv
    cbvoprab1.1
    nfan
    nfex
    @11
    vx
    vy
    @10
    wps
    vx
    @10
    vx
    nfv
    cbvoprab1.2
    nfan
    nfex
    @1
    @8
    wceq
    #
    @5
    @11
    vy
    @14
    @4
    @10
    wph
    wps
    @14
    @3
    @9
    @0
    @1
    @8
    @2
    opeq1
    eqeq2d
    cbvoprab1.3
    anbi12d
    exbidv
    cbvex
    opabbii
    wph
    vx
    vy
    vz
    vv
    dfoprab2
    wps
    vw
    vy
    vz
    vv
    dfoprab2
    3eqtr4i
end
