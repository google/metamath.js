include "cop.mm"
include "csn.mm"
include "ccnv.mm"
include "relcnv.mm"
include "cv.mm"
include "wcel.mm"
include "vex.mm"
include "opelcnv.mm"
include "wceq.mm"
include "wa.mm"
include "ancom.mm"
include "opth.mm"
include "3bitr4i.mm"
include "opex.mm"
include "elsn.mm"
include "bitri.mm"
include "eqrelriiv.mm"

theorem cnvcnvsn
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- `' `' { <. A , B >. } = `' { <. B , A >. }

  proof
    vx
    vy
    cA
    cB
    cop
    #
    csn
    #
    ccnv
    #
    ccnv
    #
    cB
    cA
    cop
    #
    csn
    #
    ccnv
    #
    @2
    relcnv
    @5
    relcnv
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @3
    wcel
    @8
    @7
    cop
    #
    @2
    wcel
    #
    @9
    @6
    wcel
    #
    @7
    @8
    @2
    vx
    vex
    #
    vy
    vex
    #
    opelcnv
    @9
    @1
    wcel
    #
    @10
    @5
    wcel
    #
    @11
    @12
    @9
    @0
    wceq
    #
    @10
    @4
    wceq
    #
    @15
    @16
    @7
    cA
    wceq
    #
    @8
    cB
    wceq
    #
    wa
    @20
    @19
    wa
    @17
    @18
    @19
    @20
    ancom
    @7
    @8
    cA
    cB
    @13
    @14
    opth
    @8
    @7
    cB
    cA
    @14
    @13
    opth
    3bitr4i
    @9
    @0
    @7
    @8
    opex
    elsn
    @10
    @4
    @8
    @7
    opex
    elsn
    3bitr4i
    @8
    @7
    @1
    @14
    @13
    opelcnv
    @7
    @8
    @5
    @13
    @14
    opelcnv
    3bitr4i
    bitri
    eqrelriiv
end
