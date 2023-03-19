include "coprab.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "df-oprab.mm"
include "nfe1.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfoprab1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- F/_ x { <. <. x , y >. , z >. | ph }

  proof
    vx
    wph
    vx
    vy
    vz
    coprab
    vw
    cv
    vx
    cv
    vy
    cv
    cop
    vz
    cv
    cop
    wceq
    wph
    wa
    vz
    wex
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
    vz
    vw
    df-oprab
    @1
    vx
    vw
    @0
    vx
    nfe1
    nfab
    nfcxfr
end
