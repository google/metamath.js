include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "opth1.mm"
include "cvv.mm"
include "wcel.mm"
include "cpr.mm"
include "csn.mm"
include "opi1.mm"
include "id.mm"
include "syl5eleq.mm"
include "oprcl.mm"
include "syl.mm"
include "simprd.mm"
include "opeq1d.mm"
include "eqtr3d.mm"
include "simpld.mm"
include "dfopg.mm"
include "sylancl.mm"
include "prex.mm"
include "preqr2.mm"
include "cv.mm"
include "wi.mm"
include "preq2.mm"
include "eqeq2d.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "vex.mm"
include "vtoclg.mm"
include "sylc.mm"
include "jca.mm"
include "opeq12.mm"
include "impbii.mm"

theorem opth
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  assume opth1.1: |- A e. _V
  assume opth1.2: |- B e. _V


  assert |- ( <. A , B >. = <. C , D >. <-> ( A = C /\ B = D ) )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    wceq
    #
    cA
    cC
    wceq
    #
    cB
    cD
    wceq
    #
    wa
    @2
    @3
    @4
    cA
    cB
    cC
    cD
    opth1.1
    opth1.2
    opth1
    #
    @2
    cD
    cvv
    wcel
    #
    cC
    cB
    cpr
    #
    cC
    cD
    cpr
    #
    wceq
    #
    @4
    @2
    cC
    cvv
    wcel
    #
    @6
    @2
    cA
    csn
    #
    @1
    wcel
    @10
    @6
    wa
    #
    @2
    @11
    @0
    @1
    cA
    cB
    opth1.1
    opth1.2
    opi1
    @2
    id
    #
    syl5eleq
    cC
    cD
    @11
    oprcl
    syl
    #
    simprd
    @2
    cC
    csn
    #
    @7
    cpr
    #
    @15
    @8
    cpr
    #
    wceq
    @9
    @2
    @1
    @16
    @17
    @2
    cC
    cB
    cop
    #
    @1
    @16
    @2
    @0
    @18
    @1
    @2
    cA
    cC
    cB
    @5
    opeq1d
    @13
    eqtr3d
    @2
    @10
    cB
    cvv
    wcel
    @18
    @16
    wceq
    @2
    @10
    @6
    @14
    simpld
    opth1.2
    cC
    cB
    cvv
    cvv
    dfopg
    sylancl
    eqtr3d
    @2
    @12
    @1
    @17
    wceq
    @14
    cC
    cD
    cvv
    cvv
    dfopg
    syl
    eqtr3d
    @7
    @8
    @15
    cC
    cB
    prex
    cC
    cD
    prex
    preqr2
    syl
    @7
    cC
    vx
    cv
    #
    cpr
    #
    wceq
    #
    cB
    @19
    wceq
    #
    wi
    @9
    @4
    wi
    vx
    cD
    cvv
    @19
    cD
    wceq
    #
    @21
    @9
    @22
    @4
    @23
    @20
    @8
    @7
    @19
    cD
    cC
    preq2
    eqeq2d
    @19
    cD
    cB
    eqeq2
    imbi12d
    cB
    @19
    cC
    opth1.2
    vx
    vex
    preqr2
    vtoclg
    sylc
    jca
    cA
    cB
    cC
    cD
    opeq12
    impbii
end
