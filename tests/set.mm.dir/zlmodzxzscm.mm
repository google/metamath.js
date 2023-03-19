include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "csn.mm"
include "cxp.mm"
include "cop.mm"
include "zring.mm"
include "cmulr.mm"
include "cfv.mm"
include "cof.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cmul.mm"
include "cvv.mm"
include "prex.mm"
include "a1i.mm"
include "wfn.mm"
include "fnconstg.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "wne.mm"
include "c0ex.mm"
include "1ex.mm"
include "pm3.2i.mm"
include "3simpc.mm"
include "0ne1.mm"
include "fnprg.mm"
include "syl3anc.mm"
include "offvalfv.mm"
include "cbs.mm"
include "eqid.mm"
include "simp1.mm"
include "zringbas.mm"
include "syl6eleq.mm"
include "zlmodzxzel.mm"
include "3adant1.mm"
include "frlmvscafval.mm"
include "ovexd.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "zringmulr.mm"
include "eqcomi.mm"
include "prid1.mm"
include "fvconst2g.mm"
include "sylancl.mm"
include "simp2.mm"
include "fvpr1g.mm"
include "oveq123d.mm"
include "sylan9eqr.mm"
include "prid2.mm"
include "simp3.mm"
include "fvpr2g.mm"
include "fmptpr.mm"
include "3eqtr4d.mm"

theorem zlmodzxzscm
  let cA: class A
  let cB: class B
  let cC: class C
  let c.xb: class .xb
  let cZ: class Z
  let vx: setvar x
  let vk: setvar k
  assume zlmodzxz.z: |- Z = ( ZZring freeLMod { 0 , 1 } )
  assume zlmodzxzscm.t: |- .xb = ( .s ` Z )


  assert |- ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) -> ( A .xb { <. 0 , B >. , <. 1 , C >. } ) = { <. 0 , ( A x. B ) >. , <. 1 , ( A x. C ) >. } )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    w3a
    #
    cc0
    c1
    cpr
    #
    cA
    csn
    cxp
    #
    cc0
    cB
    cop
    c1
    cC
    cop
    cpr
    #
    zring
    cmulr
    cfv
    #
    cof
    co
    vx
    @4
    vx
    cv
    #
    @5
    cfv
    #
    @8
    @6
    cfv
    #
    @7
    co
    #
    cmpt
    cA
    @6
    c.xb
    co
    cc0
    cA
    cB
    cmul
    co
    #
    cop
    c1
    cA
    cC
    cmul
    co
    #
    cop
    cpr
    @3
    vx
    @4
    @7
    @5
    @6
    cvv
    @4
    cvv
    wcel
    @3
    cc0
    c1
    prex
    a1i
    #
    @0
    @1
    @5
    @4
    wfn
    @2
    @4
    cA
    cz
    fnconstg
    3ad2ant1
    @3
    cc0
    cvv
    wcel
    #
    c1
    cvv
    wcel
    #
    wa
    #
    @1
    @2
    wa
    cc0
    c1
    wne
    #
    @6
    @4
    wfn
    @17
    @3
    @15
    @16
    c0ex
    1ex
    pm3.2i
    a1i
    @0
    @1
    @2
    3simpc
    @18
    @3
    0ne1
    a1i
    #
    cc0
    c1
    cB
    cC
    cvv
    cvv
    cz
    cz
    fnprg
    syl3anc
    offvalfv
    @3
    cA
    cZ
    cbs
    cfv
    #
    zring
    c.xb
    @7
    @4
    zring
    cbs
    cfv
    #
    cvv
    @6
    cZ
    zlmodzxz.z
    @20
    eqid
    @21
    eqid
    @14
    @3
    cA
    cz
    @21
    @0
    @1
    @2
    simp1
    #
    zringbas
    syl6eleq
    @1
    @2
    @6
    @20
    wcel
    @0
    cB
    cC
    cZ
    zlmodzxz.z
    zlmodzxzel
    3adant1
    zlmodzxzscm.t
    @7
    eqid
    frlmvscafval
    @3
    vx
    cc0
    c1
    @12
    @13
    @11
    cvv
    cvv
    cvv
    cvv
    @15
    @3
    c0ex
    a1i
    #
    @16
    @3
    1ex
    a1i
    #
    @3
    cA
    cB
    cmul
    ovexd
    @3
    cA
    cC
    cmul
    ovexd
    @8
    cc0
    wceq
    #
    @3
    @11
    cc0
    @5
    cfv
    #
    cc0
    @6
    cfv
    #
    @7
    co
    @12
    @25
    @9
    @26
    @10
    @27
    @7
    @8
    cc0
    @5
    fveq2
    @8
    cc0
    @6
    fveq2
    oveq12d
    @3
    @26
    cA
    @27
    cB
    @7
    cmul
    @7
    cmul
    wceq
    @3
    cmul
    @7
    zringmulr
    eqcomi
    a1i
    #
    @3
    @0
    cc0
    @4
    wcel
    @26
    cA
    wceq
    @22
    cc0
    c1
    c0ex
    prid1
    @4
    cA
    cc0
    cz
    fvconst2g
    sylancl
    @3
    @15
    @1
    @18
    @27
    cB
    wceq
    @23
    @0
    @1
    @2
    simp2
    @19
    cc0
    c1
    cB
    cC
    cvv
    cz
    fvpr1g
    syl3anc
    oveq123d
    sylan9eqr
    @8
    c1
    wceq
    #
    @3
    @11
    c1
    @5
    cfv
    #
    c1
    @6
    cfv
    #
    @7
    co
    @13
    @29
    @9
    @30
    @10
    @31
    @7
    @8
    c1
    @5
    fveq2
    @8
    c1
    @6
    fveq2
    oveq12d
    @3
    @30
    cA
    @31
    cC
    @7
    cmul
    @28
    @3
    @0
    c1
    @4
    wcel
    @30
    cA
    wceq
    @22
    cc0
    c1
    1ex
    prid2
    @4
    cA
    c1
    cz
    fvconst2g
    sylancl
    @3
    @16
    @2
    @18
    @31
    cC
    wceq
    @24
    @0
    @1
    @2
    simp3
    @19
    cc0
    c1
    cB
    cC
    cvv
    cz
    fvpr2g
    syl3anc
    oveq123d
    sylan9eqr
    fmptpr
    3eqtr4d
end
