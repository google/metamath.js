include "copab.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "df-opab.mm"
include "nfe1.mm"
include "nfex.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfopab2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- F/_ y { <. x , y >. | ph }

  proof
    vy
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
    #
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
    @2
    vy
    vz
    @1
    vy
    vx
    @0
    vy
    nfe1
    nfex
    nfab
    nfcxfr
end
