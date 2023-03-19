include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "wne.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wo.mm"
include "coutsideof.mm"
include "wi.mm"
include "simpll.mm"
include "simplr.mm"
include "simprr.mm"
include "3jca.mm"
include "simplr1.mm"
include "simplr3.mm"
include "df-3an.mm"
include "simp1.mm"
include "simp3r.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3l.mm"
include "simpr2.mm"
include "simpr3.mm"
include "btwnexchand.mm"
include "orcd.mm"
include "sylan2br.mm"
include "expr.mm"
include "simprlr.mm"
include "btwnconn3.mm"
include "syl122anc.mm"
include "adantr.mm"
include "mp2and.mm"
include "jaod.mm"
include "simpll2.mm"
include "adantl.mm"
include "necomd.mm"
include "btwnconn1.mm"
include "mp3and.mm"
include "olcd.mm"
include "imp32.mm"
include "exp31.mm"
include "syl5.mm"
include "impd.mm"
include "wb.mm"
include "broutsideof2.mm"
include "syl13anc.mm"
include "anbi12d.mm"
include "anbi12i.mm"
include "an4.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "3imtr4d.mm"

theorem outsideoftr
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ P e. ( EE ` N ) ) ) -> ( ( P OutsideOf <. A , B >. /\ P OutsideOf <. B , C >. ) -> P OutsideOf <. A , C >. ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    wa
    #
    cC
    @1
    wcel
    #
    cP
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cP
    wne
    #
    cB
    cP
    wne
    #
    wa
    #
    @10
    cC
    cP
    wne
    #
    wa
    #
    wa
    #
    cA
    cP
    cB
    cop
    #
    cbtwn
    wbr
    #
    cB
    cP
    cA
    cop
    #
    cbtwn
    wbr
    #
    wo
    #
    cB
    cP
    cC
    cop
    #
    cbtwn
    wbr
    #
    cC
    @15
    cbtwn
    wbr
    #
    wo
    #
    wa
    #
    wa
    #
    @9
    @12
    cA
    @20
    cbtwn
    wbr
    #
    cC
    @17
    cbtwn
    wbr
    #
    wo
    #
    w3a
    #
    cP
    cA
    cB
    cop
    coutsideof
    wbr
    #
    cP
    cB
    cC
    cop
    coutsideof
    wbr
    #
    wa
    #
    cP
    cA
    cC
    cop
    coutsideof
    wbr
    #
    @8
    @14
    @24
    @29
    @14
    @9
    @10
    @12
    w3a
    #
    @8
    @24
    @29
    wi
    @14
    @9
    @10
    @12
    @9
    @10
    @13
    simpll
    @9
    @10
    @13
    simplr
    @11
    @10
    @12
    simprr
    3jca
    @8
    @34
    @24
    @29
    @8
    @34
    wa
    #
    @24
    wa
    @9
    @12
    @28
    @9
    @10
    @12
    @8
    @24
    simplr1
    @9
    @10
    @12
    @8
    @24
    simplr3
    @35
    @19
    @23
    @28
    @35
    @16
    @23
    @28
    wi
    #
    @18
    @8
    @34
    @16
    @36
    @8
    @34
    @16
    wa
    #
    wa
    @21
    @28
    @22
    @8
    @37
    @21
    @28
    @37
    @21
    wa
    @8
    @34
    @16
    @21
    w3a
    #
    @28
    @34
    @16
    @21
    df-3an
    @8
    @38
    wa
    @26
    @27
    @8
    @38
    cP
    cA
    cB
    cC
    cN
    @0
    @4
    @7
    simp1
    #
    @0
    @4
    @5
    @6
    simp3r
    #
    @0
    @2
    @3
    @7
    simp2l
    #
    @0
    @2
    @3
    @7
    simp2r
    #
    @0
    @4
    @5
    @6
    simp3l
    #
    @8
    @34
    @16
    @21
    simpr2
    @8
    @34
    @16
    @21
    simpr3
    btwnexchand
    orcd
    sylan2br
    expr
    @8
    @37
    @22
    @28
    @8
    @37
    @22
    wa
    #
    wa
    @16
    @22
    @28
    @8
    @34
    @16
    @22
    simprlr
    @8
    @37
    @22
    simprr
    @8
    @16
    @22
    wa
    @28
    wi
    #
    @44
    @8
    @0
    @6
    @2
    @5
    @3
    @45
    @39
    @40
    @41
    @43
    @42
    cP
    cA
    cC
    cB
    cN
    btwnconn3
    syl122anc
    adantr
    mp2and
    expr
    jaod
    expr
    @8
    @34
    @18
    @36
    @8
    @34
    @18
    wa
    #
    wa
    @21
    @28
    @22
    @8
    @46
    @21
    @28
    @8
    @46
    @21
    wa
    #
    wa
    #
    cP
    cB
    wne
    #
    @18
    @21
    @28
    @48
    cB
    cP
    @47
    @10
    @8
    @9
    @10
    @12
    @18
    @21
    simpll2
    adantl
    necomd
    @8
    @34
    @18
    @21
    simprlr
    @8
    @46
    @21
    simprr
    @8
    @49
    @18
    @21
    w3a
    @28
    wi
    #
    @47
    @8
    @0
    @6
    @3
    @2
    @5
    @50
    @39
    @40
    @42
    @41
    @43
    cP
    cB
    cA
    cC
    cN
    btwnconn1
    syl122anc
    adantr
    mp3and
    expr
    @8
    @46
    @22
    @28
    @46
    @22
    wa
    @8
    @34
    @18
    @22
    w3a
    #
    @28
    @34
    @18
    @22
    df-3an
    @8
    @51
    wa
    @27
    @26
    @8
    @51
    cP
    cC
    cB
    cA
    cN
    @39
    @40
    @43
    @42
    @41
    @8
    @34
    @18
    @22
    simpr3
    @8
    @34
    @18
    @22
    simpr2
    btwnexchand
    olcd
    sylan2br
    expr
    jaod
    expr
    jaod
    imp32
    3jca
    exp31
    syl5
    impd
    @8
    @32
    @9
    @10
    @19
    w3a
    #
    @10
    @12
    @23
    w3a
    #
    wa
    #
    @25
    @8
    @30
    @52
    @31
    @53
    @8
    @0
    @6
    @2
    @3
    @30
    @52
    wb
    @39
    @40
    @41
    @42
    cA
    cB
    cP
    cN
    broutsideof2
    syl13anc
    @8
    @0
    @6
    @3
    @5
    @31
    @53
    wb
    @39
    @40
    @42
    @43
    cB
    cC
    cP
    cN
    broutsideof2
    syl13anc
    anbi12d
    @54
    @11
    @19
    wa
    #
    @13
    @23
    wa
    #
    wa
    @25
    @52
    @55
    @53
    @56
    @9
    @10
    @19
    df-3an
    @10
    @12
    @23
    df-3an
    anbi12i
    @11
    @13
    @19
    @23
    an4
    bitr4i
    syl6bb
    @8
    @0
    @6
    @2
    @5
    @33
    @29
    wb
    @39
    @40
    @41
    @43
    cA
    cC
    cP
    cN
    broutsideof2
    syl13anc
    3imtr4d
end
