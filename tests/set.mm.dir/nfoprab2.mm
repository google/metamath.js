include "coprab.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "df-oprab.mm"
include "nfe1.mm"
include "nfex.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfoprab2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- F/_ y { <. <. x , y >. , z >. | ph }

  proof
    vy
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
    vz
    vw
    df-oprab
    @2
    vy
    vw
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
