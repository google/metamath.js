include "wrex.mm"
include "coprab.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cvv.mm"
include "df-oprab.mm"
include "rexcom4.mm"
include "r19.42v.mm"
include "exbii.mm"
include "bitri.mm"
include "bitr2i.mm"
include "abbii.mm"
include "eqtri.mm"
include "eqeltrri.mm"
include "abrexex2.mm"
include "eqeltri.mm"

theorem oprabrexex2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vv: setvar v
  assume oprabrexex2.1: |- A e. _V
  assume oprabrexex2.2: |- { <. <. x , y >. , z >. | ph } e. _V

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A v
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint v w
  disjoint ph v
  assert |- { <. <. x , y >. , z >. | E. w e. A ph } e. _V

  proof
    wph
    vw
    cA
    wrex
    #
    vx
    vy
    vz
    coprab
    #
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
    vw
    cA
    wrex
    #
    vv
    cab
    #
    cvv
    @1
    @2
    @0
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
    @8
    @0
    vx
    vy
    vz
    vv
    df-oprab
    @12
    @7
    vv
    @7
    @5
    vw
    cA
    wrex
    #
    vx
    wex
    @12
    @5
    vw
    vx
    cA
    rexcom4
    @13
    @11
    vx
    @13
    @4
    vw
    cA
    wrex
    #
    vy
    wex
    @11
    @4
    vw
    vy
    cA
    rexcom4
    @14
    @10
    vy
    @14
    @3
    vw
    cA
    wrex
    #
    vz
    wex
    @10
    @3
    vw
    vz
    cA
    rexcom4
    @15
    @9
    vz
    @2
    wph
    vw
    cA
    r19.42v
    exbii
    bitri
    exbii
    bitri
    exbii
    bitr2i
    abbii
    eqtri
    @6
    vw
    vv
    cA
    oprabrexex2.1
    wph
    vx
    vy
    vz
    coprab
    @6
    vv
    cab
    cvv
    wph
    vx
    vy
    vz
    vv
    df-oprab
    oprabrexex2.2
    eqeltrri
    abrexex2
    eqeltri
end
