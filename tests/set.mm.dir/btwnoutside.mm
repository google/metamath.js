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
include "coutsideof.mm"
include "wb.mm"
include "wo.mm"
include "df-3an.mm"
include "simpr11.mm"
include "simpr12.mm"
include "simpr13.mm"
include "simp1.mm"
include "simp3r.mm"
include "simp2l.mm"
include "simp3l.mm"
include "simpr2.mm"
include "btwncomand.mm"
include "simp2r.mm"
include "simpr3.mm"
include "wi.mm"
include "btwnconn2.mm"
include "3com23.mm"
include "adantr.mm"
include "mp3and.mm"
include "3jca.mm"
include "sylan2br.mm"
include "expr.mm"
include "simp3.mm"
include "btwnouttr2.mm"
include "syl122anc.mm"
include "btwnexch3and.mm"
include "jaod.mm"
include "syl5.mm"
include "impbid.mm"
include "broutsideof2.mm"
include "syl13anc.mm"
include "bitr4d.mm"
include "ex.mm"

theorem btwnoutside
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ P e. ( EE ` N ) ) ) -> ( ( ( A =/= P /\ B =/= P /\ C =/= P ) /\ P Btwn <. A , C >. ) -> ( P Btwn <. B , C >. <-> P OutsideOf <. A , B >. ) ) )

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
    cC
    cP
    wne
    #
    w3a
    #
    cP
    cA
    cC
    cop
    cbtwn
    wbr
    #
    wa
    #
    cP
    cB
    cC
    cop
    cbtwn
    wbr
    #
    cP
    cA
    cB
    cop
    coutsideof
    wbr
    #
    wb
    @8
    @14
    wa
    #
    @15
    @9
    @10
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
    @16
    @17
    @15
    @21
    @8
    @14
    @15
    @21
    @14
    @15
    wa
    @8
    @12
    @13
    @15
    w3a
    #
    @21
    @12
    @13
    @15
    df-3an
    @8
    @22
    wa
    #
    @9
    @10
    @20
    @9
    @10
    @11
    @13
    @15
    @8
    simpr11
    @9
    @10
    @11
    @13
    @15
    @8
    simpr12
    @23
    @11
    cP
    cC
    cA
    cop
    cbtwn
    wbr
    #
    cP
    cC
    cB
    cop
    cbtwn
    wbr
    #
    @20
    @9
    @10
    @11
    @13
    @15
    @8
    simpr13
    @8
    @22
    cP
    cA
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
    @4
    @5
    @6
    simp3l
    #
    @8
    @12
    @13
    @15
    simpr2
    btwncomand
    @8
    @22
    cP
    cB
    cC
    cN
    @26
    @27
    @0
    @2
    @3
    @7
    simp2r
    #
    @29
    @8
    @12
    @13
    @15
    simpr3
    btwncomand
    @8
    @11
    @24
    @25
    w3a
    @20
    wi
    #
    @22
    @0
    @7
    @4
    @31
    cC
    cP
    cA
    cB
    cN
    btwnconn2
    3com23
    adantr
    mp3and
    3jca
    sylan2br
    expr
    @21
    @20
    @17
    @15
    @9
    @10
    @20
    simp3
    @17
    @18
    @15
    @19
    @8
    @14
    @18
    @15
    @14
    @18
    wa
    @8
    @12
    @13
    @18
    w3a
    #
    @15
    @12
    @13
    @18
    df-3an
    @8
    @32
    wa
    @9
    cA
    cB
    cP
    cop
    cbtwn
    wbr
    #
    @13
    @15
    @9
    @10
    @11
    @13
    @18
    @8
    simpr11
    @8
    @32
    cA
    cP
    cB
    cN
    @26
    @28
    @27
    @30
    @8
    @12
    @13
    @18
    simpr3
    btwncomand
    @8
    @12
    @13
    @18
    simpr2
    @8
    @9
    @33
    @13
    w3a
    @15
    wi
    #
    @32
    @8
    @0
    @3
    @2
    @6
    @5
    @34
    @26
    @30
    @28
    @27
    @29
    cB
    cA
    cP
    cC
    cN
    btwnouttr2
    syl122anc
    adantr
    mp3and
    sylan2br
    expr
    @8
    @14
    @19
    @15
    @14
    @19
    wa
    @8
    @12
    @13
    @19
    w3a
    #
    @15
    @12
    @13
    @19
    df-3an
    @8
    @35
    cA
    cB
    cP
    cC
    cN
    @26
    @28
    @30
    @27
    @29
    @8
    @35
    cB
    cP
    cA
    cN
    @26
    @30
    @27
    @28
    @8
    @12
    @13
    @19
    simpr3
    btwncomand
    @8
    @12
    @13
    @19
    simpr2
    btwnexch3and
    sylan2br
    expr
    jaod
    syl5
    impbid
    @8
    @16
    @21
    wb
    #
    @14
    @8
    @0
    @6
    @2
    @3
    @36
    @26
    @27
    @28
    @30
    cA
    cB
    cP
    cN
    broutsideof2
    syl13anc
    adantr
    bitr4d
    ex
end
