include "coprab.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "df-oprab.mm"
include "nfv.mm"
include "nfan.mm"
include "nfex.mm"
include "nfab.mm"
include "nfcxfr.mm"

theorem nfoprab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  assume nfoprab.1: |- F/ w ph

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ph v
  assert |- F/_ w { <. <. x , y >. , z >. | ph }

  proof
    vw
    wph
    vx
    vy
    vz
    coprab
    vv
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
    #
    wph
    wa
    #
    vz
    wex
    #
    vy
    wex
    #
    vx
    wex
    #
    vv
    cab
    wph
    vx
    vy
    vz
    vv
    df-oprab
    @4
    vw
    vv
    @3
    vw
    vx
    @2
    vw
    vy
    @1
    vw
    vz
    @0
    wph
    vw
    @0
    vw
    nfv
    nfoprab.1
    nfan
    nfex
    nfex
    nfex
    nfab
    nfcxfr
end
