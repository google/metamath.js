include "wcel.mm"
include "cpw.mm"
include "ctop.mm"
include "cv.mm"
include "wne.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cha.mm"
include "distop.mm"
include "wa.mm"
include "csn.mm"
include "wss.mm"
include "simplrl.mm"
include "snssd.mm"
include "snex.mm"
include "elpw.mm"
include "sylibr.mm"
include "simplrr.mm"
include "vsnid.mm"
include "a1i.mm"
include "disjsn2.mm"
include "adantl.mm"
include "eleq2.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "3anbi13d.mm"
include "ineq2.mm"
include "3anbi23d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "ex.mm"
include "ralrimivva.mm"
include "cuni.mm"
include "unipw.mm"
include "eqcomi.mm"
include "ishaus.mm"
include "sylanbrc.mm"

theorem dishaus
  let cA: class A
  let cV: class V
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> ~P A e. Haus )

  proof
    cA
    cV
    wcel
    #
    cA
    cpw
    #
    ctop
    wcel
    vx
    cv
    #
    vy
    cv
    #
    wne
    #
    @2
    vu
    cv
    #
    wcel
    #
    @3
    vv
    cv
    #
    wcel
    #
    @5
    @7
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vv
    @1
    wrex
    vu
    @1
    wrex
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @1
    cha
    wcel
    cA
    cV
    distop
    @0
    @13
    vx
    vy
    cA
    cA
    @0
    @2
    cA
    wcel
    #
    @3
    cA
    wcel
    #
    wa
    wa
    #
    @4
    @12
    @16
    @4
    wa
    #
    @2
    csn
    #
    @1
    wcel
    #
    @3
    csn
    #
    @1
    wcel
    #
    @2
    @18
    wcel
    #
    @3
    @20
    wcel
    #
    @18
    @20
    cin
    #
    c0
    wceq
    #
    @12
    @17
    @18
    cA
    wss
    @19
    @17
    @2
    cA
    @0
    @14
    @15
    @4
    simplrl
    snssd
    @18
    cA
    @2
    snex
    elpw
    sylibr
    @17
    @20
    cA
    wss
    @21
    @17
    @3
    cA
    @0
    @14
    @15
    @4
    simplrr
    snssd
    @20
    cA
    @3
    snex
    elpw
    sylibr
    @22
    @17
    vx
    vsnid
    a1i
    @23
    @17
    vy
    vsnid
    a1i
    @4
    @25
    @16
    @2
    @3
    disjsn2
    adantl
    @11
    @22
    @23
    @25
    w3a
    @22
    @8
    @18
    @7
    cin
    #
    c0
    wceq
    #
    w3a
    vu
    vv
    @18
    @20
    @1
    @1
    @5
    @18
    wceq
    #
    @6
    @22
    @10
    @27
    @8
    @5
    @18
    @2
    eleq2
    @28
    @9
    @26
    c0
    @5
    @18
    @7
    ineq1
    eqeq1d
    3anbi13d
    @7
    @20
    wceq
    #
    @8
    @23
    @27
    @25
    @22
    @7
    @20
    @3
    eleq2
    @29
    @26
    @24
    c0
    @7
    @20
    @18
    ineq2
    eqeq1d
    3anbi23d
    rspc2ev
    syl113anc
    ex
    ralrimivva
    vx
    vy
    vv
    vu
    @1
    cA
    @1
    cuni
    cA
    cA
    unipw
    eqcomi
    ishaus
    sylanbrc
end
