include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "coutsideof.mm"
include "wbr.mm"
include "csegle.mm"
include "cbtwn.mm"
include "wb.mm"
include "cv.mm"
include "ccgr.mm"
include "wrex.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "brsegle2.mm"
include "syl122anc.mm"
include "adantr.mm"
include "wceq.mm"
include "simprl.mm"
include "outsideofcom.mm"
include "ad2antrr.mm"
include "mpbid.mm"
include "simpll.mm"
include "simplr1.mm"
include "simplr3.mm"
include "cgrrflxd.mm"
include "jca.mm"
include "ccolin.mm"
include "wn.mm"
include "simprrl.mm"
include "wi.mm"
include "simpr.mm"
include "simplr2.mm"
include "btwncolinear1.mm"
include "syl13anc.mm"
include "mpd.mm"
include "wne.mm"
include "outsidene1.mm"
include "neneqd.mm"
include "df-3an.mm"
include "simpr2l.mm"
include "btwncomand.mm"
include "btwnswapid2.mm"
include "mp2and.mm"
include "sylan2br.mm"
include "expr.mm"
include "mtod.mm"
include "broutsideof.mm"
include "sylanbrc.mm"
include "simprrr.mm"
include "outsideofeq.mm"
include "syl133anc.mm"
include "opeq2.mm"
include "breq2d.mm"
include "syl5ibrcom.mm"
include "an4s.mm"
include "rexlimdvaa.mm"
include "sylbid.mm"
include "btwnsegle.mm"
include "impbid.mm"
include "ex.mm"

theorem outsidele
  let cA: class A
  let cB: class B
  let cP: class P
  let cN: class N
  let vy: setvar y


  assert |- ( ( N e. NN /\ ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ) -> ( P OutsideOf <. A , B >. -> ( <. P , A >. Seg<_ <. P , B >. <-> A Btwn <. P , B >. ) ) )

  proof
    cN
    cn
    wcel
    #
    cP
    cN
    cee
    cfv
    #
    wcel
    #
    cA
    @1
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    wa
    #
    cP
    cA
    cB
    cop
    coutsideof
    wbr
    #
    cP
    cA
    cop
    cP
    cB
    cop
    #
    csegle
    wbr
    #
    cA
    @8
    cbtwn
    wbr
    #
    wb
    @6
    @7
    wa
    #
    @9
    @10
    @11
    @9
    cA
    cP
    vy
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    @13
    @8
    ccgr
    wbr
    #
    wa
    #
    vy
    @1
    wrex
    #
    @10
    @6
    @9
    @17
    wb
    #
    @7
    @6
    @0
    @2
    @3
    @2
    @4
    @18
    @0
    @5
    simpl
    @0
    @2
    @3
    @4
    simpr1
    #
    @0
    @2
    @3
    @4
    simpr2
    @19
    @0
    @2
    @3
    @4
    simpr3
    vy
    cP
    cA
    cP
    cB
    cN
    brsegle2
    syl122anc
    adantr
    @11
    @16
    @10
    vy
    @1
    @6
    @12
    @1
    wcel
    #
    @7
    @16
    @10
    @6
    @20
    wa
    #
    @7
    @16
    wa
    #
    wa
    #
    cB
    @12
    wceq
    #
    @10
    @23
    cP
    cB
    cA
    cop
    coutsideof
    wbr
    #
    @8
    @8
    ccgr
    wbr
    #
    wa
    #
    cP
    @12
    cA
    cop
    #
    coutsideof
    wbr
    #
    @15
    wa
    #
    @24
    @23
    @25
    @26
    @23
    @7
    @25
    @21
    @7
    @16
    simprl
    #
    @6
    @7
    @25
    wb
    @20
    @22
    cA
    cB
    cP
    cN
    outsideofcom
    ad2antrr
    mpbid
    @21
    @26
    @22
    @21
    cP
    cB
    cN
    @0
    @5
    @20
    simpll
    #
    @2
    @3
    @4
    @0
    @20
    simplr1
    #
    @2
    @3
    @4
    @0
    @20
    simplr3
    #
    cgrrflxd
    adantr
    jca
    @23
    @29
    @15
    @23
    cP
    @28
    ccolin
    wbr
    #
    cP
    @28
    cbtwn
    wbr
    #
    wn
    @29
    @23
    @14
    @35
    @21
    @7
    @14
    @15
    simprrl
    #
    @21
    @14
    @35
    wi
    #
    @22
    @21
    @0
    @2
    @20
    @3
    @38
    @32
    @33
    @6
    @20
    simpr
    #
    @2
    @3
    @4
    @0
    @20
    simplr2
    #
    cP
    @12
    cA
    cN
    btwncolinear1
    syl13anc
    adantr
    mpd
    @23
    @36
    cA
    cP
    wceq
    #
    @23
    cA
    cP
    @23
    @7
    cA
    cP
    wne
    #
    @31
    @6
    @7
    @42
    wi
    @20
    @22
    cA
    cB
    cP
    cN
    outsidene1
    ad2antrr
    mpd
    neneqd
    @21
    @22
    @36
    @41
    @22
    @36
    wa
    @21
    @7
    @16
    @36
    w3a
    #
    @41
    @7
    @16
    @36
    df-3an
    @21
    @43
    wa
    cA
    @12
    cP
    cop
    cbtwn
    wbr
    #
    @36
    @41
    @21
    @43
    cA
    cP
    @12
    cN
    @32
    @40
    @33
    @39
    @14
    @15
    @7
    @36
    @21
    simpr2l
    btwncomand
    @21
    @7
    @16
    @36
    simpr3
    @21
    @44
    @36
    wa
    @41
    wi
    #
    @43
    @21
    @0
    @3
    @20
    @2
    @45
    @32
    @40
    @39
    @33
    cA
    @12
    cP
    cN
    btwnswapid2
    syl13anc
    adantr
    mp2and
    sylan2br
    expr
    mtod
    @12
    cA
    cP
    broutsideof
    sylanbrc
    @21
    @7
    @14
    @15
    simprrr
    jca
    @21
    @27
    @30
    wa
    @24
    wi
    #
    @22
    @21
    @0
    @2
    @3
    @2
    @4
    @4
    @20
    @46
    @32
    @33
    @40
    @33
    @34
    @34
    @39
    cP
    cP
    cB
    cA
    cN
    cB
    @12
    outsideofeq
    syl133anc
    adantr
    mp2and
    @23
    @10
    @24
    @14
    @37
    @24
    @8
    @13
    cA
    cbtwn
    cB
    @12
    cP
    opeq2
    breq2d
    syl5ibrcom
    mpd
    an4s
    rexlimdvaa
    sylbid
    @6
    @10
    @9
    wi
    @7
    cP
    cA
    cB
    cN
    btwnsegle
    adantr
    impbid
    ex
end
