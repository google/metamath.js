include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "cbtwn.mm"
include "csegle.mm"
include "wb.mm"
include "wi.mm"
include "btwnsegle.mm"
include "3anrev.mm"
include "sylan2b.mm"
include "3ancoma.mm"
include "btwncom.mm"
include "ccgr.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr3.mm"
include "cgrrflx2d.mm"
include "simpr1.mm"
include "seglecgr12.mm"
include "syl333anc.mm"
include "mp2and.mm"
include "3imtr4d.mm"
include "jcad.mm"
include "adantr.mm"
include "w3o.mm"
include "brcolinear.mm"
include "wceq.mm"
include "simprl.mm"
include "btwncomand.mm"
include "biimpa.mm"
include "adantrl.mm"
include "3anrot.mm"
include "sylan2br.mm"
include "sylbid.mm"
include "imp.mm"
include "adantrr.mm"
include "segleantisym.mm"
include "syl122anc.mm"
include "endofsegidand.mm"
include "btwntriv1.mm"
include "3adant3r2.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "mpd.mm"
include "expr.mm"
include "adantld.mm"
include "ex.mm"
include "biimprd.mm"
include "a1dd.mm"
include "simprr.mm"
include "3ancomb.mm"
include "btwntriv2.mm"
include "adantrd.mm"
include "3jaod.mm"
include "impbid.mm"

theorem colinbtwnle
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) -> ( A Colinear <. B , C >. -> ( B Btwn <. A , C >. <-> ( <. A , B >. Seg<_ <. A , C >. /\ <. B , C >. Seg<_ <. A , C >. ) ) ) )

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
    cC
    @1
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cop
    #
    ccolin
    wbr
    #
    cB
    cA
    cC
    cop
    #
    cbtwn
    wbr
    #
    cA
    cB
    cop
    #
    @9
    csegle
    wbr
    #
    @7
    @9
    csegle
    wbr
    #
    wa
    #
    wb
    @6
    @8
    wa
    @10
    @14
    @6
    @10
    @14
    wi
    @8
    @6
    @10
    @12
    @13
    cA
    cB
    cC
    cN
    btwnsegle
    @6
    cB
    cC
    cA
    cop
    #
    cbtwn
    wbr
    #
    cC
    cB
    cop
    #
    @15
    csegle
    wbr
    #
    @10
    @13
    @5
    @0
    @4
    @3
    @2
    w3a
    @16
    @18
    wi
    @2
    @3
    @4
    3anrev
    cC
    cB
    cA
    cN
    btwnsegle
    sylan2b
    @5
    @0
    @3
    @2
    @4
    w3a
    @10
    @16
    wb
    @2
    @3
    @4
    3ancoma
    cB
    cA
    cC
    cN
    btwncom
    sylan2b
    #
    @6
    @7
    @17
    ccgr
    wbr
    #
    @9
    @15
    ccgr
    wbr
    #
    @13
    @18
    wb
    #
    @6
    cB
    cC
    cN
    @0
    @5
    simpl
    #
    @0
    @2
    @3
    @4
    simpr2
    #
    @0
    @2
    @3
    @4
    simpr3
    #
    cgrrflx2d
    @6
    cA
    cC
    cN
    @23
    @0
    @2
    @3
    @4
    simpr1
    #
    @25
    cgrrflx2d
    @6
    @0
    @3
    @4
    @2
    @4
    @4
    @3
    @4
    @2
    @20
    @21
    wa
    @22
    wi
    @23
    @24
    @25
    @26
    @25
    @25
    @24
    @25
    @26
    cB
    cC
    cA
    cC
    cC
    cB
    cC
    cA
    cN
    seglecgr12
    syl333anc
    mp2and
    #
    3imtr4d
    jcad
    adantr
    @6
    @8
    @14
    @10
    wi
    #
    @6
    @8
    cA
    @7
    cbtwn
    wbr
    #
    @16
    cC
    @11
    cbtwn
    wbr
    #
    w3o
    @28
    cA
    cB
    cC
    cN
    brcolinear
    @6
    @29
    @28
    @16
    @30
    @6
    @29
    @28
    @6
    @29
    wa
    @13
    @10
    @12
    @6
    @29
    @13
    @10
    @6
    @29
    @13
    wa
    #
    wa
    #
    cB
    cA
    wceq
    #
    @10
    @6
    @31
    cC
    cB
    cA
    cN
    @23
    @25
    @24
    @26
    @6
    @31
    cA
    cB
    cC
    cN
    @23
    @26
    @24
    @25
    @6
    @29
    @13
    simprl
    btwncomand
    @32
    @18
    @15
    @17
    csegle
    wbr
    #
    @17
    @15
    ccgr
    wbr
    #
    @6
    @13
    @18
    @29
    @6
    @13
    @18
    @27
    biimpa
    adantrl
    @6
    @29
    @34
    @13
    @6
    @29
    @34
    @6
    @29
    cA
    @17
    cbtwn
    wbr
    #
    @34
    cA
    cB
    cC
    cN
    btwncom
    @5
    @0
    @4
    @2
    @3
    w3a
    @36
    @34
    wi
    @4
    @2
    @3
    3anrot
    cC
    cA
    cB
    cN
    btwnsegle
    sylan2br
    sylbid
    imp
    adantrr
    @6
    @18
    @34
    wa
    @35
    wi
    #
    @31
    @6
    @0
    @4
    @3
    @4
    @2
    @37
    @23
    @25
    @24
    @25
    @26
    cC
    cB
    cC
    cA
    cN
    segleantisym
    syl122anc
    adantr
    mp2and
    endofsegidand
    @6
    @33
    @10
    wi
    @31
    @6
    @10
    @33
    cA
    @9
    cbtwn
    wbr
    #
    @0
    @2
    @4
    @38
    @3
    cA
    cC
    cN
    btwntriv1
    3adant3r2
    cB
    cA
    @9
    cbtwn
    breq1
    syl5ibrcom
    adantr
    mpd
    expr
    adantld
    ex
    @6
    @16
    @10
    @14
    @6
    @10
    @16
    @19
    biimprd
    a1dd
    @6
    @30
    @28
    @6
    @30
    wa
    @12
    @10
    @13
    @6
    @30
    @12
    @10
    @6
    @30
    @12
    wa
    #
    wa
    #
    cB
    cC
    wceq
    #
    @10
    @6
    @39
    cA
    cB
    cC
    cN
    @23
    @26
    @24
    @25
    @6
    @30
    @12
    simprl
    @40
    @12
    @9
    @11
    csegle
    wbr
    #
    @11
    @9
    ccgr
    wbr
    #
    @6
    @30
    @12
    simprr
    @6
    @30
    @42
    @12
    @6
    @30
    @42
    @5
    @0
    @2
    @4
    @3
    w3a
    @30
    @42
    wi
    @2
    @3
    @4
    3ancomb
    cA
    cC
    cB
    cN
    btwnsegle
    sylan2b
    imp
    adantrr
    @6
    @12
    @42
    wa
    @43
    wi
    #
    @39
    @6
    @0
    @2
    @3
    @2
    @4
    @44
    @23
    @26
    @24
    @26
    @25
    cA
    cB
    cA
    cC
    cN
    segleantisym
    syl122anc
    adantr
    mp2and
    endofsegidand
    @6
    @41
    @10
    wi
    @39
    @6
    @10
    @41
    cC
    @9
    cbtwn
    wbr
    #
    @0
    @2
    @4
    @45
    @3
    cA
    cC
    cN
    btwntriv2
    3adant3r2
    cB
    cC
    @9
    cbtwn
    breq1
    syl5ibrcom
    adantr
    mpd
    expr
    adantrd
    ex
    3jaod
    sylbid
    imp
    impbid
    ex
end
