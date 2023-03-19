include "cvv.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "elxp.mm"
include "ancom.mm"
include "2exbii.mm"
include "19.42vv.mm"
include "elvv.mm"
include "anbi2i.mm"
include "vex.mm"
include "biantru.mm"
include "3bitr2i.mm"
include "anass.mm"
include "3bitrri.mm"
include "exrot4.mm"
include "excom.mm"
include "opex.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "ceqsexv.mm"
include "exbii.mm"
include "bitri.mm"

theorem elvvv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  assert |- ( A e. ( ( _V X. _V ) X. _V ) <-> E. x E. y E. z A = <. <. x , y >. , z >. )

  proof
    cA
    cvv
    cvv
    cxp
    #
    cvv
    cxp
    wcel
    cA
    vw
    cv
    #
    vz
    cv
    #
    cop
    #
    wceq
    #
    @1
    @0
    wcel
    #
    @2
    cvv
    wcel
    #
    wa
    wa
    #
    vz
    wex
    vw
    wex
    #
    cA
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @2
    cop
    #
    wceq
    #
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    vw
    vz
    cA
    @0
    cvv
    elxp
    @8
    @1
    @11
    wceq
    #
    @4
    wa
    #
    vy
    wex
    vx
    wex
    #
    vz
    wex
    vw
    wex
    @17
    vz
    wex
    vw
    wex
    #
    vy
    wex
    vx
    wex
    @15
    @7
    @18
    vw
    vz
    @18
    @4
    @16
    wa
    #
    vy
    wex
    vx
    wex
    #
    @4
    @5
    wa
    #
    @6
    wa
    #
    @7
    @17
    @20
    vx
    vy
    @16
    @4
    ancom
    2exbii
    @21
    @4
    @16
    vy
    wex
    vx
    wex
    #
    wa
    @22
    @23
    @4
    @16
    vx
    vy
    19.42vv
    @5
    @24
    @4
    vx
    vy
    @1
    elvv
    anbi2i
    @6
    @22
    vz
    vex
    biantru
    3bitr2i
    @4
    @5
    @6
    anass
    3bitrri
    2exbii
    @17
    vx
    vy
    vw
    vz
    exrot4
    @19
    @14
    vx
    vy
    @19
    @17
    vw
    wex
    #
    vz
    wex
    @14
    @17
    vw
    vz
    excom
    @25
    @13
    vz
    @4
    @13
    vw
    @11
    @9
    @10
    opex
    @16
    @3
    @12
    cA
    @1
    @11
    @2
    opeq1
    eqeq2d
    ceqsexv
    exbii
    bitri
    2exbii
    3bitr2i
    bitri
end
