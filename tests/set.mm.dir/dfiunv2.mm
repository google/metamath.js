include "ciun.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "wceq.mm"
include "df-iun.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "vex.mm"
include "weq.mm"
include "eleq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "rexbii.mm"
include "abbii.mm"
include "3eqtri.mm"

theorem dfiunv2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w

  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint C w
  assert |- U_ x e. A U_ y e. B C = { z | E. x e. A E. y e. B z e. C }

  proof
    vx
    cA
    vy
    cB
    cC
    ciun
    #
    ciun
    vx
    cA
    vw
    cv
    #
    cC
    wcel
    #
    vy
    cB
    wrex
    #
    vw
    cab
    #
    ciun
    vz
    cv
    #
    @4
    wcel
    #
    vx
    cA
    wrex
    #
    vz
    cab
    @5
    cC
    wcel
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    vz
    cab
    vx
    cA
    @0
    @4
    @0
    @4
    wceq
    vx
    cv
    cA
    wcel
    vy
    vw
    cB
    cC
    df-iun
    a1i
    iuneq2i
    vx
    vz
    cA
    @4
    df-iun
    @7
    @10
    vz
    @6
    @9
    vx
    cA
    @3
    @9
    vw
    @5
    vz
    vex
    vw
    vz
    weq
    @2
    @8
    vy
    cB
    @1
    @5
    cC
    eleq1
    rexbidv
    elab
    rexbii
    abbii
    3eqtri
end
