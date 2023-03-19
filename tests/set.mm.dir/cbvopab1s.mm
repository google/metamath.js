include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "wsb.mm"
include "copab.mm"
include "nfv.mm"
include "nfs1v.mm"
include "nfan.mm"
include "nfex.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "sbequ12.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "cbvex.mm"
include "abbii.mm"
include "df-opab.mm"
include "3eqtr4i.mm"

theorem cbvopab1s
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  assert |- { <. x , y >. | ph } = { <. z , y >. | [ z / x ] ph }

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
    vz
    cv
    #
    @2
    cop
    #
    wceq
    #
    wph
    vx
    vz
    wsb
    #
    wa
    #
    vy
    wex
    #
    vz
    wex
    #
    vw
    cab
    wph
    vx
    vy
    copab
    @11
    vz
    vy
    copab
    @7
    @14
    vw
    @6
    @13
    vx
    vz
    @6
    vz
    nfv
    @12
    vx
    vy
    @10
    @11
    vx
    @10
    vx
    nfv
    wph
    vx
    vz
    nfs1v
    nfan
    nfex
    @1
    @8
    wceq
    #
    @5
    @12
    vy
    @15
    @4
    @10
    wph
    @11
    @15
    @3
    @9
    @0
    @1
    @8
    @2
    opeq1
    eqeq2d
    wph
    vx
    vz
    sbequ12
    anbi12d
    exbidv
    cbvex
    abbii
    wph
    vx
    vy
    vw
    df-opab
    @11
    vz
    vy
    vw
    df-opab
    3eqtr4i
end
