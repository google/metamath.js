include "copab.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "df-opab.mm"
include "nfe1.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfopab1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- F/_ x { <. x , y >. | ph }

  proof
    vx
    wph
    vx
    vy
    copab
    vz
    cv
    vx
    cv
    vy
    cv
    cop
    wceq
    wph
    wa
    vy
    wex
    #
    vx
    wex
    #
    vz
    cab
    wph
    vx
    vy
    vz
    df-opab
    @1
    vx
    vz
    @0
    vx
    nfe1
    nfab
    nfcxfr
end
