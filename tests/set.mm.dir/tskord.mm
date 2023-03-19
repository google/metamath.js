include "con0.mm"
include "wcel.mm"
include "ctsk.mm"
include "csdm.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi2d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "wral.mm"
include "simplrl.mm"
include "cdom.mm"
include "wss.mm"
include "onelss.mm"
include "ssdomg.mm"
include "syld.mm"
include "imp.mm"
include "adantlr.mm"
include "simplrr.mm"
include "domsdomtr.mm"
include "syl2anc.mm"
include "pm2.27.mm"
include "ralimdva.mm"
include "dfss3.mm"
include "tskssel.mm"
include "3exp.mm"
include "syl5bir.mm"
include "com23.mm"
include "adantl.mm"
include "ex.mm"
include "tfis3.mm"
include "3impib.mm"
include "3com12.mm"

theorem tskord
  let cA: class A
  let cT: class T
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( T e. Tarski /\ A e. On /\ A ~< T ) -> A e. T )

  proof
    cA
    con0
    wcel
    #
    cT
    ctsk
    wcel
    #
    cA
    cT
    csdm
    wbr
    #
    cA
    cT
    wcel
    #
    @0
    @1
    @2
    @3
    @1
    vx
    cv
    #
    cT
    csdm
    wbr
    #
    wa
    #
    @4
    cT
    wcel
    #
    wi
    @1
    vy
    cv
    #
    cT
    csdm
    wbr
    #
    wa
    #
    @8
    cT
    wcel
    #
    wi
    #
    @1
    @2
    wa
    #
    @3
    wi
    vx
    vy
    cA
    @4
    @8
    wceq
    #
    @6
    @10
    @7
    @11
    @14
    @5
    @9
    @1
    @4
    @8
    cT
    csdm
    breq1
    anbi2d
    @4
    @8
    cT
    eleq1
    imbi12d
    @4
    cA
    wceq
    #
    @6
    @13
    @7
    @3
    @15
    @5
    @2
    @1
    @4
    cA
    cT
    csdm
    breq1
    anbi2d
    @4
    cA
    cT
    eleq1
    imbi12d
    @4
    con0
    wcel
    #
    @6
    @12
    vy
    @4
    wral
    #
    @7
    @16
    @6
    @17
    @7
    wi
    @16
    @6
    wa
    #
    @17
    @11
    vy
    @4
    wral
    #
    @7
    @18
    @12
    @11
    vy
    @4
    @18
    @8
    @4
    wcel
    #
    wa
    #
    @1
    @9
    @12
    @11
    wi
    @16
    @1
    @5
    @20
    simplrl
    @21
    @8
    @4
    cdom
    wbr
    #
    @5
    @9
    @16
    @20
    @22
    @6
    @16
    @20
    @22
    @16
    @20
    @8
    @4
    wss
    @22
    @4
    @8
    onelss
    @8
    @4
    con0
    ssdomg
    syld
    imp
    adantlr
    @16
    @1
    @5
    @20
    simplrr
    @8
    @4
    cT
    domsdomtr
    syl2anc
    @10
    @11
    pm2.27
    syl2anc
    ralimdva
    @6
    @19
    @7
    wi
    #
    @16
    @1
    @5
    @23
    @1
    @19
    @5
    @7
    @19
    @4
    cT
    wss
    #
    @1
    @5
    @7
    wi
    vy
    @4
    cT
    dfss3
    @1
    @24
    @5
    @7
    @4
    cT
    tskssel
    3exp
    syl5bir
    com23
    imp
    adantl
    syld
    ex
    com23
    tfis3
    3impib
    3com12
end
