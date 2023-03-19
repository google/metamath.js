include "cuni.mm"
include "cdm.mm"
include "cv.mm"
include "ciun.mm"
include "cop.mm"
include "wcel.mm"
include "wex.mm"
include "wrex.mm"
include "wa.mm"
include "excom.mm"
include "ancom.mm"
include "19.41v.mm"
include "vex.mm"
include "eldm2.mm"
include "anbi2i.mm"
include "3bitr4i.mm"
include "exbii.mm"
include "bitri.mm"
include "eluni.mm"
include "df-rex.mm"
include "eliun.mm"
include "eqriv.mm"

theorem dmuni
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- dom U. A = U_ x e. A dom x

  proof
    vy
    cA
    cuni
    #
    cdm
    #
    vx
    cA
    vx
    cv
    #
    cdm
    #
    ciun
    #
    vy
    cv
    #
    vz
    cv
    cop
    #
    @0
    wcel
    #
    vz
    wex
    #
    @5
    @3
    wcel
    #
    vx
    cA
    wrex
    #
    @5
    @1
    wcel
    @5
    @4
    wcel
    @6
    @2
    wcel
    #
    @2
    cA
    wcel
    #
    wa
    #
    vx
    wex
    #
    vz
    wex
    #
    @12
    @9
    wa
    #
    vx
    wex
    #
    @8
    @10
    @15
    @13
    vz
    wex
    #
    vx
    wex
    @17
    @13
    vz
    vx
    excom
    @18
    @16
    vx
    @11
    vz
    wex
    #
    @12
    wa
    @12
    @19
    wa
    @18
    @16
    @19
    @12
    ancom
    @11
    @12
    vz
    19.41v
    @9
    @19
    @12
    vz
    @5
    @2
    vy
    vex
    #
    eldm2
    anbi2i
    3bitr4i
    exbii
    bitri
    @7
    @14
    vz
    vx
    @6
    cA
    eluni
    exbii
    @9
    vx
    cA
    df-rex
    3bitr4i
    vz
    @5
    @0
    @20
    eldm2
    vx
    @5
    cA
    @3
    eliun
    3bitr4i
    eqriv
end
