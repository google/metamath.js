include "cnr.mm"
include "wcel.mm"
include "c0r.mm"
include "wne.mm"
include "cmr.mm"
include "co.mm"
include "cltr.mm"
include "wbr.mm"
include "wo.mm"
include "wceq.mm"
include "wn.mm"
include "wb.mm"
include "0r.mm"
include "wor.mm"
include "wa.mm"
include "ltsosr.mm"
include "sotrieq.mm"
include "mpan.mm"
include "mpan2.mm"
include "necon2abid.mm"
include "cm1r.mm"
include "cplr.mm"
include "m1r.mm"
include "mulclsr.mm"
include "ltasr.mm"
include "syl.mm"
include "addcomsr.mm"
include "pn0sr.mm"
include "syl5eq.mm"
include "0idsr.mm"
include "breq12d.mm"
include "bitrd.mm"
include "mulgt0sr.mm"
include "anidms.mm"
include "syl6bi.mm"
include "c1r.mm"
include "mulcomsr.mm"
include "oveq1i.mm"
include "mulasssr.mm"
include "3eqtr3i.mm"
include "m1m1sr.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "3eqtr4i.mm"
include "1idsr.mm"
include "breq2d.mm"
include "sylibd.mm"
include "wi.mm"
include "a1i.mm"
include "jaod.mm"
include "sylbird.mm"
include "imp.mm"

theorem sqgt0sr
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. R. /\ A =/= 0R ) -> 0R <R ( A .R A ) )

  proof
    cA
    cnr
    wcel
    #
    cA
    c0r
    wne
    #
    c0r
    cA
    cA
    cmr
    co
    #
    cltr
    wbr
    #
    @0
    @1
    cA
    c0r
    cltr
    wbr
    #
    c0r
    cA
    cltr
    wbr
    #
    wo
    #
    @3
    @0
    @6
    cA
    c0r
    @0
    c0r
    cnr
    wcel
    #
    cA
    c0r
    wceq
    @6
    wn
    wb
    #
    0r
    cnr
    cltr
    wor
    @0
    @7
    wa
    @8
    ltsosr
    cnr
    cA
    c0r
    cltr
    sotrieq
    mpan
    mpan2
    necon2abid
    @0
    @4
    @3
    @5
    @0
    @4
    c0r
    cA
    cm1r
    cmr
    co
    #
    @9
    cmr
    co
    #
    cltr
    wbr
    #
    @3
    @0
    @4
    c0r
    @9
    cltr
    wbr
    #
    @11
    @0
    @4
    @9
    cA
    cplr
    co
    #
    @9
    c0r
    cplr
    co
    #
    cltr
    wbr
    #
    @12
    @0
    @9
    cnr
    wcel
    #
    @4
    @15
    wb
    @0
    cm1r
    cnr
    wcel
    @16
    m1r
    cA
    cm1r
    mulclsr
    mpan2
    #
    cA
    c0r
    @9
    ltasr
    syl
    @0
    @13
    c0r
    @14
    @9
    cltr
    @0
    @13
    cA
    @9
    cplr
    co
    c0r
    @9
    cA
    addcomsr
    cA
    pn0sr
    syl5eq
    @0
    @16
    @14
    @9
    wceq
    @17
    @9
    0idsr
    syl
    breq12d
    bitrd
    @12
    @11
    @9
    @9
    mulgt0sr
    anidms
    syl6bi
    @0
    @10
    @2
    c0r
    cltr
    @0
    @10
    @2
    c1r
    cmr
    co
    #
    @2
    cA
    cm1r
    @9
    cmr
    co
    #
    cmr
    co
    cA
    cA
    c1r
    cmr
    co
    #
    cmr
    co
    @10
    @18
    @19
    @20
    cA
    cmr
    @19
    cA
    cm1r
    cm1r
    cmr
    co
    #
    cmr
    co
    #
    @20
    cm1r
    cA
    cmr
    co
    #
    cm1r
    cmr
    co
    @9
    cm1r
    cmr
    co
    @19
    @22
    @23
    @9
    cm1r
    cmr
    cm1r
    cA
    mulcomsr
    oveq1i
    cm1r
    cA
    cm1r
    mulasssr
    cA
    cm1r
    cm1r
    mulasssr
    3eqtr3i
    @21
    c1r
    cA
    cmr
    m1m1sr
    oveq2i
    eqtri
    oveq2i
    cA
    cm1r
    @9
    mulasssr
    cA
    cA
    c1r
    mulasssr
    3eqtr4i
    @0
    @18
    @2
    wceq
    #
    @0
    @0
    wa
    @2
    cnr
    wcel
    @24
    cA
    cA
    mulclsr
    @2
    1idsr
    syl
    anidms
    syl5eq
    breq2d
    sylibd
    @5
    @3
    wi
    @0
    @5
    @3
    cA
    cA
    mulgt0sr
    anidms
    a1i
    jaod
    sylbird
    imp
end
