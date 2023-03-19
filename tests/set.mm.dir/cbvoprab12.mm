include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "coprab.mm"
include "nfv.mm"
include "nfan.mm"
include "opeq12.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvex2.mm"
include "opabbii.mm"
include "dfoprab2.mm"
include "3eqtr4i.mm"

theorem cbvoprab12
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  assume cbvoprab12.1: |- F/ w ph
  assume cbvoprab12.2: |- F/ v ph
  assume cbvoprab12.3: |- F/ x ps
  assume cbvoprab12.4: |- F/ y ps
  assume cbvoprab12.5: |- ( ( x = w /\ y = v ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint w z
  disjoint v z
  disjoint v w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint u w
  disjoint u v
  disjoint ph u
  disjoint ps u
  assert |- { <. <. x , y >. , z >. | ph } = { <. <. w , v >. , z >. | ps }

  proof
    vu
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
    vx
    wex
    #
    vu
    vz
    copab
    @0
    vw
    cv
    #
    vv
    cv
    #
    cop
    #
    wceq
    #
    wps
    wa
    #
    vv
    wex
    vw
    wex
    #
    vu
    vz
    copab
    wph
    vx
    vy
    vz
    coprab
    wps
    vw
    vv
    vz
    coprab
    @6
    @12
    vu
    vz
    @5
    @11
    vx
    vy
    vw
    vv
    @4
    wph
    vw
    @4
    vw
    nfv
    cbvoprab12.1
    nfan
    @4
    wph
    vv
    @4
    vv
    nfv
    cbvoprab12.2
    nfan
    @10
    wps
    vx
    @10
    vx
    nfv
    cbvoprab12.3
    nfan
    @10
    wps
    vy
    @10
    vy
    nfv
    cbvoprab12.4
    nfan
    @1
    @7
    wceq
    @2
    @8
    wceq
    wa
    #
    @4
    @10
    wph
    wps
    @13
    @3
    @9
    @0
    @1
    @2
    @7
    @8
    opeq12
    eqeq2d
    cbvoprab12.5
    anbi12d
    cbvex2
    opabbii
    wph
    vx
    vy
    vz
    vu
    dfoprab2
    wps
    vw
    vv
    vz
    vu
    dfoprab2
    3eqtr4i
end
