include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "coe.mm"
include "co.mm"
include "wi.mm"
include "cv.mm"
include "csuc.mm"
include "wa.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "c1o.mm"
include "0lt1o.mm"
include "oe0.mm"
include "syl5eleqr.mm"
include "adantr.mm"
include "comu.mm"
include "simpl.mm"
include "oecl.mm"
include "jca.mm"
include "omordi.mm"
include "wb.mm"
include "om0.mm"
include "eleq1d.mm"
include "ad2antlr.mm"
include "sylibd.mm"
include "sylan.mm"
include "oesuc.mm"
include "sylibrd.mm"
include "exp31.mm"
include "com12.mm"
include "com34.mm"
include "impd.mm"
include "wlim.mm"
include "wral.mm"
include "wss.mm"
include "ciun.mm"
include "wrex.mm"
include "0ellim.mm"
include "eqimss2.mm"
include "syl.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "syl2an.mm"
include "ssiun.mm"
include "adantrr.mm"
include "cvv.mm"
include "vex.mm"
include "oelim.mm"
include "mpanlr1.mm"
include "anasss.mm"
include "an12s.mm"
include "sseqtr4d.mm"
include "word.mm"
include "limelon.mm"
include "mpan.mm"
include "ancoms.mm"
include "eloni.mm"
include "ordgt0ge1.mm"
include "3syl.mm"
include "mpbird.mm"
include "ex.mm"
include "a1dd.mm"
include "tfinds3.mm"
include "expd.mm"
include "imp31.mm"

theorem oen0
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( A e. On /\ B e. On ) /\ (/) e. A ) -> (/) e. ( A ^o B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    c0
    cA
    wcel
    #
    c0
    cA
    cB
    coe
    co
    #
    wcel
    #
    @1
    @0
    @2
    @4
    wi
    @1
    @0
    @2
    @4
    c0
    cA
    vx
    cv
    #
    coe
    co
    #
    wcel
    #
    c0
    cA
    c0
    coe
    co
    #
    wcel
    #
    c0
    cA
    vy
    cv
    #
    coe
    co
    #
    wcel
    #
    c0
    cA
    @10
    csuc
    #
    coe
    co
    #
    wcel
    #
    @4
    @0
    @2
    wa
    #
    vx
    vy
    cB
    @5
    c0
    wceq
    @6
    @8
    c0
    @5
    c0
    cA
    coe
    oveq2
    eleq2d
    @5
    @10
    wceq
    @6
    @11
    c0
    @5
    @10
    cA
    coe
    oveq2
    eleq2d
    @5
    @13
    wceq
    @6
    @14
    c0
    @5
    @13
    cA
    coe
    oveq2
    eleq2d
    @5
    cB
    wceq
    @6
    @3
    c0
    @5
    cB
    cA
    coe
    oveq2
    eleq2d
    @0
    @9
    @2
    @0
    c0
    c1o
    @8
    0lt1o
    cA
    oe0
    #
    syl5eleqr
    adantr
    @10
    con0
    wcel
    #
    @0
    @2
    @12
    @15
    wi
    @18
    @0
    @12
    @2
    @15
    @0
    @18
    @12
    @2
    @15
    wi
    #
    wi
    @0
    @18
    @12
    @19
    @0
    @18
    wa
    #
    @12
    wa
    @2
    c0
    @11
    cA
    comu
    co
    #
    wcel
    #
    @15
    @20
    @0
    @11
    con0
    wcel
    #
    wa
    #
    @12
    @2
    @22
    wi
    @20
    @0
    @23
    @0
    @18
    simpl
    cA
    @10
    oecl
    jca
    @24
    @12
    wa
    @2
    @11
    c0
    comu
    co
    #
    @21
    wcel
    #
    @22
    c0
    cA
    @11
    omordi
    @23
    @26
    @22
    wb
    @0
    @12
    @23
    @25
    c0
    @21
    @11
    om0
    eleq1d
    ad2antlr
    sylibd
    sylan
    @20
    @15
    @22
    wb
    @12
    @20
    @14
    @21
    c0
    cA
    @10
    oesuc
    eleq2d
    adantr
    sylibrd
    exp31
    com12
    com34
    impd
    @5
    wlim
    #
    @16
    @7
    @12
    vy
    @5
    wral
    @27
    @16
    @7
    @27
    @16
    wa
    #
    @7
    c1o
    @6
    wss
    #
    @28
    c1o
    vy
    @5
    @11
    ciun
    #
    @6
    @27
    @0
    c1o
    @30
    wss
    #
    @2
    @27
    @0
    wa
    #
    c1o
    @11
    wss
    #
    vy
    @5
    wrex
    #
    @31
    @27
    c0
    @5
    wcel
    c1o
    @8
    wss
    #
    @34
    @0
    @5
    0ellim
    @0
    @8
    c1o
    wceq
    @35
    @17
    c1o
    @8
    eqimss2
    syl
    @33
    @35
    vy
    c0
    @5
    @10
    c0
    wceq
    @11
    @8
    c1o
    @10
    c0
    cA
    coe
    oveq2
    sseq2d
    rspcev
    syl2an
    vy
    @5
    @11
    c1o
    ssiun
    syl
    adantrr
    @0
    @27
    @2
    @6
    @30
    wceq
    #
    @0
    @27
    @2
    @36
    @0
    @5
    cvv
    wcel
    #
    @27
    @2
    @36
    vx
    vex
    #
    vy
    cA
    @5
    cvv
    oelim
    mpanlr1
    anasss
    an12s
    sseqtr4d
    @27
    @0
    @7
    @29
    wb
    #
    @2
    @32
    @6
    con0
    wcel
    #
    @6
    word
    @39
    @27
    @5
    con0
    wcel
    #
    @0
    @40
    @37
    @27
    @41
    @38
    @5
    cvv
    limelon
    mpan
    @0
    @41
    @40
    cA
    @5
    oecl
    ancoms
    sylan
    @6
    eloni
    @6
    ordgt0ge1
    3syl
    adantrr
    mpbird
    ex
    a1dd
    tfinds3
    expd
    com12
    imp31
end
