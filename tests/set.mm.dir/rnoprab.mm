include "coprab.mm"
include "crn.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "cab.mm"
include "dfoprab2.mm"
include "rneqi.mm"
include "rnopab.mm"
include "exrot3.mm"
include "opex.mm"
include "isseti.mm"
include "19.41v.mm"
include "mpbiran.mm"
include "2exbii.mm"
include "bitri.mm"
include "abbii.mm"
include "3eqtri.mm"

theorem rnoprab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w z
  disjoint w y
  disjoint ph w
  assert |- ran { <. <. x , y >. , z >. | ph } = { z | E. x E. y ph }

  proof
    wph
    vx
    vy
    vz
    coprab
    #
    crn
    vw
    cv
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
    vw
    vz
    copab
    #
    crn
    @6
    vw
    wex
    #
    vz
    cab
    wph
    vy
    wex
    vx
    wex
    #
    vz
    cab
    @0
    @7
    wph
    vx
    vy
    vz
    vw
    dfoprab2
    rneqi
    @6
    vw
    vz
    rnopab
    @8
    @9
    vz
    @8
    @5
    vw
    wex
    #
    vy
    wex
    vx
    wex
    @9
    @5
    vw
    vx
    vy
    exrot3
    @10
    wph
    vx
    vy
    @10
    @4
    vw
    wex
    wph
    vw
    @3
    @1
    @2
    opex
    isseti
    @4
    wph
    vw
    19.41v
    mpbiran
    2exbii
    bitri
    abbii
    3eqtri
end
