include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "df-rex.mm"
include "vex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "anbi1i.mm"
include "r19.41v.mm"
include "bitr4i.mm"
include "exbii.mm"
include "bitri.mm"
include "rexcom4.mm"
include "eqeq2d.mm"
include "ceqsexv.mm"
include "rexbii.mm"
include "abbii.mm"

theorem abrexco
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume abrexco.1: |- B e. _V
  assume abrexco.2: |- ( y = B -> C = D )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint D y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint w z
  assert |- { x | E. y e. { z | E. w e. A z = B } x = C } = { x | E. w e. A x = D }

  proof
    vx
    cv
    #
    cC
    wceq
    #
    vy
    vz
    cv
    #
    cB
    wceq
    #
    vw
    cA
    wrex
    #
    vz
    cab
    #
    wrex
    #
    @0
    cD
    wceq
    #
    vw
    cA
    wrex
    #
    vx
    @6
    vy
    cv
    #
    cB
    wceq
    #
    @1
    wa
    #
    vy
    wex
    #
    vw
    cA
    wrex
    #
    @8
    @6
    @11
    vw
    cA
    wrex
    #
    vy
    wex
    #
    @13
    @6
    @9
    @5
    wcel
    #
    @1
    wa
    #
    vy
    wex
    @15
    @1
    vy
    @5
    df-rex
    @17
    @14
    vy
    @17
    @10
    vw
    cA
    wrex
    #
    @1
    wa
    @14
    @16
    @18
    @1
    @4
    @18
    vz
    @9
    vy
    vex
    @2
    @9
    wceq
    @3
    @10
    vw
    cA
    @2
    @9
    cB
    eqeq1
    rexbidv
    elab
    anbi1i
    @10
    @1
    vw
    cA
    r19.41v
    bitr4i
    exbii
    bitri
    @11
    vw
    vy
    cA
    rexcom4
    bitr4i
    @12
    @7
    vw
    cA
    @1
    @7
    vy
    cB
    abrexco.1
    @10
    cC
    cD
    @0
    abrexco.2
    eqeq2d
    ceqsexv
    rexbii
    bitri
    abbii
end
