include "cv.mm"
include "copab.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "ciun.mm"
include "elopab.mm"
include "rexbii.mm"
include "rexcom4.mm"
include "r19.42v.mm"
include "exbii.mm"
include "bitri.mm"
include "abbii.mm"
include "df-iun.mm"
include "df-opab.mm"
include "3eqtr4i.mm"

theorem iunopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint y z
  disjoint x z
  disjoint ph w
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- U_ z e. A { <. x , y >. | ph } = { <. x , y >. | E. z e. A ph }

  proof
    vw
    cv
    #
    wph
    vx
    vy
    copab
    #
    wcel
    #
    vz
    cA
    wrex
    #
    vw
    cab
    @0
    vx
    cv
    vy
    cv
    cop
    wceq
    #
    wph
    vz
    cA
    wrex
    #
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
    vz
    cA
    @1
    ciun
    @5
    vx
    vy
    copab
    @3
    @8
    vw
    @3
    @4
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
    cA
    wrex
    #
    @8
    @2
    @11
    vz
    cA
    wph
    vx
    vy
    @0
    elopab
    rexbii
    @12
    @10
    vz
    cA
    wrex
    #
    vx
    wex
    @8
    @10
    vz
    vx
    cA
    rexcom4
    @13
    @7
    vx
    @13
    @9
    vz
    cA
    wrex
    #
    vy
    wex
    @7
    @9
    vz
    vy
    cA
    rexcom4
    @14
    @6
    vy
    @4
    wph
    vz
    cA
    r19.42v
    exbii
    bitri
    exbii
    bitri
    bitri
    abbii
    vz
    vw
    cA
    @1
    df-iun
    @5
    vx
    vy
    vw
    df-opab
    3eqtr4i
end
