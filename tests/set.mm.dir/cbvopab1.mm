include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "copab.mm"
include "wsb.mm"
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
include "nfsb.mm"
include "sbequ.mm"
include "sbie.mm"
include "syl6bb.mm"
include "bitri.mm"
include "abbii.mm"
include "df-opab.mm"
include "3eqtr4i.mm"

theorem cbvopab1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vw: setvar w
  assume cbvopab1.1: |- F/ z ph
  assume cbvopab1.2: |- F/ x ps
  assume cbvopab1.3: |- ( x = z -> ( ph <-> ps ) )

  disjoint x y
  disjoint y z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint v z
  disjoint w z
  disjoint ph v
  disjoint ph w
  disjoint ps v
  disjoint ps w
  assert |- { <. x , y >. | ph } = { <. z , y >. | ps }

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
    wps
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
    wps
    vz
    vy
    copab
    @7
    @13
    vw
    @7
    @0
    vv
    cv
    #
    @2
    cop
    #
    wceq
    #
    wph
    vx
    vv
    wsb
    #
    wa
    #
    vy
    wex
    #
    vv
    wex
    @13
    @6
    @19
    vx
    vv
    @6
    vv
    nfv
    @18
    vx
    vy
    @16
    @17
    vx
    @16
    vx
    nfv
    wph
    vx
    vv
    nfs1v
    nfan
    nfex
    @1
    @14
    wceq
    #
    @5
    @18
    vy
    @20
    @4
    @16
    wph
    @17
    @20
    @3
    @15
    @0
    @1
    @14
    @2
    opeq1
    eqeq2d
    wph
    vx
    vv
    sbequ12
    anbi12d
    exbidv
    cbvex
    @19
    @12
    vv
    vz
    @18
    vz
    vy
    @16
    @17
    vz
    @16
    vz
    nfv
    wph
    vx
    vv
    vz
    cbvopab1.1
    nfsb
    nfan
    nfex
    @12
    vv
    nfv
    @14
    @8
    wceq
    #
    @18
    @11
    vy
    @21
    @16
    @10
    @17
    wps
    @21
    @15
    @9
    @0
    @14
    @8
    @2
    opeq1
    eqeq2d
    @21
    @17
    wph
    vx
    vz
    wsb
    wps
    wph
    vv
    vz
    vx
    sbequ
    wph
    wps
    vx
    vz
    cbvopab1.2
    cbvopab1.3
    sbie
    syl6bb
    anbi12d
    exbidv
    cbvex
    bitri
    abbii
    wph
    vx
    vy
    vw
    df-opab
    wps
    vz
    vy
    vw
    df-opab
    3eqtr4i
end
