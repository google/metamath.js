include "copab.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "df-opab.mm"
include "nfv.mm"
include "nfan.mm"
include "nfex.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume nfopab.1: |- F/ z ph

  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w z
  disjoint w y
  disjoint ph w
  assert |- F/_ z { <. x , y >. | ph }

  proof
    vz
    wph
    vx
    vy
    copab
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
    #
    vx
    wex
    #
    vw
    cab
    wph
    vx
    vy
    vw
    df-opab
    @3
    vz
    vw
    @2
    vz
    vx
    @1
    vz
    vy
    @0
    wph
    vz
    @0
    vz
    nfv
    nfopab.1
    nfan
    nfex
    nfex
    nfab
    nfcxfr
end
