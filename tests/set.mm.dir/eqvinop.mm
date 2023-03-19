include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "opth2.mm"
include "anbi2i.mm"
include "ancom.mm"
include "anass.mm"
include "3bitri.mm"
include "exbii.mm"
include "19.42v.mm"
include "opeq2.mm"
include "eqeq2d.mm"
include "ceqsexv.mm"
include "opeq1.mm"
include "bitr2i.mm"

theorem eqvinop
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqvinop.1: |- B e. _V
  assume eqvinop.2: |- C e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( A = <. B , C >. <-> E. x E. y ( A = <. x , y >. /\ <. x , y >. = <. B , C >. ) )

  proof
    cA
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
    @2
    cB
    cC
    cop
    #
    wceq
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    @0
    cB
    wceq
    #
    cA
    @0
    cC
    cop
    #
    wceq
    #
    wa
    #
    vx
    wex
    cA
    @4
    wceq
    #
    @7
    @11
    vx
    @7
    @8
    @1
    cC
    wceq
    #
    @3
    wa
    #
    wa
    #
    vy
    wex
    @8
    @14
    vy
    wex
    #
    wa
    @11
    @6
    @15
    vy
    @6
    @3
    @8
    @13
    wa
    #
    wa
    @17
    @3
    wa
    @15
    @5
    @17
    @3
    @0
    @1
    cB
    cC
    eqvinop.1
    eqvinop.2
    opth2
    anbi2i
    @3
    @17
    ancom
    @8
    @13
    @3
    anass
    3bitri
    exbii
    @8
    @14
    vy
    19.42v
    @16
    @10
    @8
    @3
    @10
    vy
    cC
    eqvinop.2
    @13
    @2
    @9
    cA
    @1
    cC
    @0
    opeq2
    eqeq2d
    ceqsexv
    anbi2i
    3bitri
    exbii
    @10
    @12
    vx
    cB
    eqvinop.1
    @8
    @9
    @4
    cA
    @0
    cB
    cC
    opeq1
    eqeq2d
    ceqsexv
    bitr2i
end
