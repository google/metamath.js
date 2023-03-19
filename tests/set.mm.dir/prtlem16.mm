include "cdm.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wex.mm"
include "wa.mm"
include "wrex.mm"
include "vex.mm"
include "eldm.mm"
include "prtlem13.mm"
include "exbii.mm"
include "elunii.mm"
include "ancoms.mm"
include "adantrr.mm"
include "rexlimiva.mm"
include "exlimiv.mm"
include "eluni2.mm"
include "weq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "pm4.24.mm"
include "syl6bbr.mm"
include "rexbidv.mm"
include "spcev.mm"
include "sylbi.mm"
include "impbii.mm"
include "3bitri.mm"
include "eqriv.mm"

theorem prtlem16
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cA: class A
  let c.sm: class .~
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume prtlem13.1: |- .~ = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) }

  disjoint u x
  disjoint u y
  disjoint A u
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint u v
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint v w
  disjoint w x
  disjoint w y
  disjoint v z
  disjoint x z
  disjoint y z
  disjoint u w
  disjoint u z
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint .~ w
  disjoint .~ z
  assert |- dom .~ = U. A

  proof
    vz
    c.sm
    cdm
    #
    cA
    cuni
    #
    vz
    cv
    #
    @0
    wcel
    @2
    vw
    cv
    #
    c.sm
    wbr
    #
    vw
    wex
    @2
    vv
    cv
    #
    wcel
    #
    @3
    @5
    wcel
    #
    wa
    #
    vv
    cA
    wrex
    #
    vw
    wex
    #
    @2
    @1
    wcel
    #
    vw
    @2
    c.sm
    vz
    vex
    #
    eldm
    @4
    @9
    vw
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    c.sm
    prtlem13.1
    prtlem13
    exbii
    @10
    @11
    @9
    @11
    vw
    @8
    @11
    vv
    cA
    @5
    cA
    wcel
    #
    @6
    @11
    @7
    @6
    @13
    @11
    @2
    @5
    cA
    elunii
    ancoms
    adantrr
    rexlimiva
    exlimiv
    @11
    @6
    vv
    cA
    wrex
    #
    @10
    vv
    @2
    cA
    eluni2
    @9
    @14
    vw
    @2
    @12
    vw
    vz
    weq
    #
    @8
    @6
    vv
    cA
    @15
    @8
    @6
    @6
    wa
    @6
    @15
    @7
    @6
    @6
    @3
    @2
    @5
    eleq1
    anbi2d
    @6
    pm4.24
    syl6bbr
    rexbidv
    spcev
    sylbi
    impbii
    3bitri
    eqriv
end
