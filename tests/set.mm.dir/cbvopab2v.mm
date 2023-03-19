include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "copab.mm"
include "opeq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvexv.mm"
include "exbii.mm"
include "abbii.mm"
include "df-opab.mm"
include "3eqtr4i.mm"

theorem cbvopab2v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume cbvopab2v.1: |- ( y = z -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph z
  disjoint ps y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint ps w
  assert |- { <. x , y >. | ph } = { <. x , z >. | ps }

  proof
    vw
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
    vw
    cab
    @0
    @1
    vz
    cv
    #
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
    vx
    wex
    #
    vw
    cab
    wph
    vx
    vy
    copab
    wps
    vx
    vz
    copab
    @7
    @13
    vw
    @6
    @12
    vx
    @5
    @11
    vy
    vz
    @2
    @8
    wceq
    #
    @4
    @10
    wph
    wps
    @14
    @3
    @9
    @0
    @2
    @8
    @1
    opeq2
    eqeq2d
    cbvopab2v.1
    anbi12d
    cbvexv
    exbii
    abbii
    wph
    vx
    vy
    vw
    df-opab
    wps
    vx
    vz
    vw
    df-opab
    3eqtr4i
end
