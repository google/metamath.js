include "cop.mm"
include "coutsideof.mm"
include "wbr.mm"
include "ccolin.mm"
include "cbtwn.mm"
include "wn.mm"
include "wa.mm"
include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wne.mm"
include "wo.mm"
include "broutsideof.mm"
include "wceq.mm"
include "btwntriv1.mm"
include "3adant3r1.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "necon3bd.mm"
include "imp.mm"
include "adantrl.mm"
include "btwntriv2.mm"
include "w3o.mm"
include "wi.mm"
include "brcolinear.mm"
include "pm2.24.mm"
include "a1i.mm"
include "wb.mm"
include "3anrot.mm"
include "btwncom.mm"
include "sylan2b.mm"
include "orc.mm"
include "syl6bi.mm"
include "a1dd.mm"
include "olc.mm"
include "a1d.mm"
include "3jaod.mm"
include "sylbid.mm"
include "imp32.mm"
include "3jca.mm"
include "simp3.mm"
include "3ancomb.mm"
include "btwncolinear2.mm"
include "btwncolinear1.mm"
include "jaod.mm"
include "syl5.mm"
include "simpr2.mm"
include "neneqd.mm"
include "simprl1.mm"
include "simprr.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr3.mm"
include "btwnswapid.mm"
include "syl13anc.mm"
include "adantr.mm"
include "mp2and.mm"
include "expr.mm"
include "mtod.mm"
include "3exp2.mm"
include "btwncomand.mm"
include "sylan2br.mm"
include "com12.mm"
include "com4l.mm"
include "3imp2.mm"
include "jca.mm"
include "impbida.mm"
include "syl5bb.mm"

theorem broutsideof2
  let cA: class A
  let cB: class B
  let cP: class P
  let cN: class N


  assert |- ( ( N e. NN /\ ( P e. ( EE ` N ) /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) ) -> ( P OutsideOf <. A , B >. <-> ( A =/= P /\ B =/= P /\ ( A Btwn <. P , B >. \/ B Btwn <. P , A >. ) ) ) )

  proof
    cP
    cA
    cB
    cop
    #
    coutsideof
    wbr
    cP
    @0
    ccolin
    wbr
    #
    cP
    @0
    cbtwn
    wbr
    #
    wn
    #
    wa
    #
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
    @6
    wcel
    #
    cB
    @6
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cP
    wne
    #
    cB
    cP
    wne
    #
    cA
    cP
    cB
    cop
    cbtwn
    wbr
    #
    cB
    cP
    cA
    cop
    cbtwn
    wbr
    #
    wo
    #
    w3a
    #
    cA
    cB
    cP
    broutsideof
    @11
    @4
    @17
    @11
    @4
    wa
    @12
    @13
    @16
    @11
    @3
    @12
    @1
    @11
    @3
    @12
    @11
    @2
    cA
    cP
    @11
    cA
    @0
    cbtwn
    wbr
    #
    cA
    cP
    wceq
    #
    @2
    @5
    @8
    @9
    @18
    @7
    cA
    cB
    cN
    btwntriv1
    3adant3r1
    cA
    cP
    @0
    cbtwn
    breq1
    syl5ibcom
    necon3bd
    imp
    adantrl
    @11
    @3
    @13
    @1
    @11
    @3
    @13
    @11
    @2
    cB
    cP
    @11
    cB
    @0
    cbtwn
    wbr
    #
    cB
    cP
    wceq
    #
    @2
    @5
    @8
    @9
    @20
    @7
    cA
    cB
    cN
    btwntriv2
    3adant3r1
    cB
    cP
    @0
    cbtwn
    breq1
    syl5ibcom
    necon3bd
    imp
    adantrl
    @11
    @1
    @3
    @16
    @11
    @1
    @2
    cA
    cB
    cP
    cop
    cbtwn
    wbr
    #
    @15
    w3o
    @3
    @16
    wi
    #
    cP
    cA
    cB
    cN
    brcolinear
    @11
    @2
    @23
    @22
    @15
    @2
    @23
    wi
    @11
    @2
    @16
    pm2.24
    a1i
    @11
    @22
    @16
    @3
    @11
    @22
    @14
    @16
    @10
    @5
    @8
    @9
    @7
    w3a
    @22
    @14
    wb
    @7
    @8
    @9
    3anrot
    cA
    cB
    cP
    cN
    btwncom
    sylan2b
    @14
    @15
    orc
    syl6bi
    a1dd
    @15
    @23
    wi
    @11
    @15
    @16
    @3
    @15
    @14
    olc
    a1d
    a1i
    3jaod
    sylbid
    imp32
    3jca
    @11
    @17
    wa
    @1
    @3
    @11
    @17
    @1
    @17
    @16
    @11
    @1
    @12
    @13
    @16
    simp3
    @11
    @14
    @1
    @15
    @10
    @5
    @7
    @9
    @8
    w3a
    @14
    @1
    wi
    @7
    @8
    @9
    3ancomb
    cP
    cB
    cA
    cN
    btwncolinear2
    sylan2b
    cP
    cA
    cB
    cN
    btwncolinear1
    jaod
    syl5
    imp
    @11
    @12
    @13
    @16
    @3
    @16
    @11
    @12
    @13
    @3
    @11
    @16
    @12
    @13
    @3
    wi
    wi
    #
    @11
    @14
    @24
    @15
    @11
    @14
    @12
    @13
    @3
    @11
    @14
    @12
    @13
    w3a
    #
    wa
    #
    @2
    @19
    @26
    cA
    cP
    @11
    @14
    @12
    @13
    simpr2
    neneqd
    @11
    @25
    @2
    @19
    @11
    @25
    @2
    wa
    #
    wa
    @14
    @2
    @19
    @14
    @12
    @13
    @2
    @11
    simprl1
    @11
    @25
    @2
    simprr
    @11
    @14
    @2
    wa
    @19
    wi
    #
    @27
    @11
    @5
    @8
    @7
    @9
    @28
    @5
    @10
    simpl
    #
    @5
    @7
    @8
    @9
    simpr2
    #
    @5
    @7
    @8
    @9
    simpr1
    #
    @5
    @7
    @8
    @9
    simpr3
    #
    cA
    cP
    cB
    cN
    btwnswapid
    syl13anc
    adantr
    mp2and
    expr
    mtod
    3exp2
    @11
    @15
    @12
    @13
    @3
    @11
    @15
    @12
    @13
    w3a
    #
    wa
    #
    @2
    @21
    @34
    cB
    cP
    @11
    @15
    @12
    @13
    simpr3
    neneqd
    @11
    @33
    @2
    @21
    @11
    @33
    @2
    wa
    #
    wa
    @15
    cP
    cB
    cA
    cop
    cbtwn
    wbr
    #
    @21
    @15
    @12
    @13
    @2
    @11
    simprl1
    @11
    @35
    cP
    cA
    cB
    cN
    @29
    @31
    @30
    @32
    @11
    @33
    @2
    simprr
    btwncomand
    @11
    @15
    @36
    wa
    @21
    wi
    #
    @35
    @10
    @5
    @9
    @7
    @8
    w3a
    @37
    @9
    @7
    @8
    3anrot
    cB
    cP
    cA
    cN
    btwnswapid
    sylan2br
    adantr
    mp2and
    expr
    mtod
    3exp2
    jaod
    com12
    com4l
    3imp2
    jca
    impbida
    syl5bb
end
