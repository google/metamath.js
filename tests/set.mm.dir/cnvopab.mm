include "copab.mm"
include "ccnv.mm"
include "relcnv.mm"
include "relopab.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wsb.mm"
include "opelopabsbALT.mm"
include "sbcom2.mm"
include "bitri.mm"
include "vex.mm"
include "opelcnv.mm"
include "3bitr4i.mm"
include "eqrelriiv.mm"

theorem cnvopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint ph z
  disjoint ph w
  assert |- `' { <. x , y >. | ph } = { <. y , x >. | ph }

  proof
    vz
    vw
    wph
    vx
    vy
    copab
    #
    ccnv
    #
    wph
    vy
    vx
    copab
    #
    @0
    relcnv
    wph
    vy
    vx
    relopab
    vw
    cv
    #
    vz
    cv
    #
    cop
    @0
    wcel
    #
    wph
    vy
    vz
    wsb
    vx
    vw
    wsb
    #
    @4
    @3
    cop
    #
    @1
    wcel
    @7
    @2
    wcel
    @5
    wph
    vx
    vw
    wsb
    vy
    vz
    wsb
    @6
    wph
    vx
    vy
    vw
    vz
    opelopabsbALT
    wph
    vx
    vw
    vy
    vz
    sbcom2
    bitri
    @4
    @3
    @0
    vz
    vex
    vw
    vex
    opelcnv
    wph
    vy
    vx
    vz
    vw
    opelopabsbALT
    3bitr4i
    eqrelriiv
end
