include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "copab.mm"
include "nfv.mm"
include "nfan.mm"
include "opeq12.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvex2.mm"
include "abbii.mm"
include "df-opab.mm"
include "3eqtr4i.mm"

theorem cbvopab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assume cbvopab.1: |- F/ z ph
  assume cbvopab.2: |- F/ w ph
  assume cbvopab.3: |- F/ x ps
  assume cbvopab.4: |- F/ y ps
  assume cbvopab.5: |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) )

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
  assert |- { <. x , y >. | ph } = { <. z , w >. | ps }

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
    vx
    wex
    #
    vv
    cab
    @0
    vz
    cv
    #
    vw
    cv
    #
    cop
    #
    wceq
    #
    wps
    wa
    #
    vw
    wex
    vz
    wex
    #
    vv
    cab
    wph
    vx
    vy
    copab
    wps
    vz
    vw
    copab
    @6
    @12
    vv
    @5
    @11
    vx
    vy
    vz
    vw
    @4
    wph
    vz
    @4
    vz
    nfv
    cbvopab.1
    nfan
    @4
    wph
    vw
    @4
    vw
    nfv
    cbvopab.2
    nfan
    @10
    wps
    vx
    @10
    vx
    nfv
    cbvopab.3
    nfan
    @10
    wps
    vy
    @10
    vy
    nfv
    cbvopab.4
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
    cbvopab.5
    anbi12d
    cbvex2
    abbii
    wph
    vx
    vy
    vv
    df-opab
    wps
    vz
    vw
    vv
    df-opab
    3eqtr4i
end
