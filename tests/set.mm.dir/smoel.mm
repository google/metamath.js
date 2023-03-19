include "wsmo.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "wi.mm"
include "word.mm"
include "smodm.mm"
include "ordtr1.mm"
include "ancomsd.mm"
include "expdimp.mm"
include "sylan.mm"
include "con0.mm"
include "wf.mm"
include "cv.mm"
include "wral.mm"
include "w3a.mm"
include "df-smo.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "eleq2.mm"
include "eleq2d.mm"
include "rspc2v.mm"
include "ancoms.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "sylbi.mm"
include "syld.mm"
include "pm2.43d.mm"
include "3impia.mm"

theorem smoel
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let cF: class F


  assert |- ( ( Smo B /\ A e. dom B /\ C e. A ) -> ( B ` C ) e. ( B ` A ) )

  proof
    cB
    wsmo
    #
    cA
    cB
    cdm
    #
    wcel
    #
    cC
    cA
    wcel
    #
    cC
    cB
    cfv
    #
    cA
    cB
    cfv
    #
    wcel
    #
    @0
    @2
    wa
    #
    @3
    @6
    @7
    @3
    cC
    @1
    wcel
    #
    @3
    @6
    wi
    #
    @0
    @1
    word
    #
    @2
    @3
    @8
    wi
    cB
    smodm
    @10
    @2
    @3
    @8
    @10
    @3
    @2
    @8
    cC
    cA
    @1
    ordtr1
    ancomsd
    expdimp
    sylan
    @0
    @2
    @8
    @9
    @0
    @1
    con0
    cB
    wf
    #
    @10
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @12
    cB
    cfv
    #
    @13
    cB
    cfv
    #
    wcel
    #
    wi
    #
    vy
    @1
    wral
    vx
    @1
    wral
    #
    w3a
    @2
    @8
    wa
    #
    @9
    wi
    #
    vx
    vy
    cB
    df-smo
    @19
    @11
    @21
    @10
    @20
    @19
    @9
    @8
    @2
    @19
    @9
    wi
    @18
    @9
    cC
    @13
    wcel
    #
    @4
    @16
    wcel
    #
    wi
    vx
    vy
    cC
    cA
    @1
    @1
    @12
    cC
    wceq
    #
    @14
    @22
    @17
    @23
    @12
    cC
    @13
    eleq1
    @24
    @15
    @4
    @16
    @12
    cC
    cB
    fveq2
    eleq1d
    imbi12d
    @13
    cA
    wceq
    #
    @22
    @3
    @23
    @6
    @13
    cA
    cC
    eleq2
    @25
    @16
    @5
    @4
    @13
    cA
    cB
    fveq2
    eleq2d
    imbi12d
    rspc2v
    ancoms
    com12
    3ad2ant3
    sylbi
    expdimp
    syld
    pm2.43d
    3impia
end
