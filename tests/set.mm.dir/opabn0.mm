include "copab.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "elopab.mm"
include "exbii.mm"
include "exrot3.mm"
include "opex.mm"
include "isseti.mm"
include "19.41v.mm"
include "mpbiran.mm"
include "2exbii.mm"
include "bitri.mm"

theorem opabn0
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( { <. x , y >. | ph } =/= (/) <-> E. x E. y ph )

  proof
    wph
    vx
    vy
    copab
    #
    c0
    wne
    vz
    cv
    #
    @0
    wcel
    #
    vz
    wex
    #
    wph
    vy
    wex
    vx
    wex
    #
    vz
    @0
    n0
    @3
    @1
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
    vz
    wex
    #
    @4
    @2
    @10
    vz
    wph
    vx
    vy
    @1
    elopab
    exbii
    @11
    @9
    vz
    wex
    #
    vy
    wex
    vx
    wex
    @4
    @9
    vz
    vx
    vy
    exrot3
    @12
    wph
    vx
    vy
    @12
    @8
    vz
    wex
    wph
    vz
    @7
    @5
    @6
    opex
    isseti
    @8
    wph
    vz
    19.41v
    mpbiran
    2exbii
    bitri
    bitri
    bitri
end
