include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "simplr.mm"
include "wi.mm"
include "0re.mm"
include "ltletr.mm"
include "mp3an1.mm"
include "imp.mm"
include "gt0ne0d.mm"
include "rereccld.mm"
include "wne.mm"
include "gt0ne0.mm"
include "rereccl.mm"
include "syldan.mm"
include "ad2ant2r.mm"
include "recgt0.mm"
include "syl2anc.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "simprr.mm"
include "wb.mm"
include "id.mm"
include "lerec.mm"
include "syl12anc.mm"
include "mpbid.mm"
include "jca.mm"
include "jca31.mm"
include "simplll.mm"
include "simplrl.mm"
include "simpllr.mm"
include "simprll.mm"
include "simprrl.mm"
include "simprlr.mm"
include "jca32.mm"
include "simplrr.mm"
include "simprrr.mm"
include "lemul12a.mm"
include "sylc.mm"
include "sylan2.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "divrecd.mm"
include "adantlr.mm"
include "ad2antrl.mm"
include "adantrrr.mm"
include "adantrlr.mm"
include "adantll.mm"
include "3brtr4d.mm"

theorem lediv12a
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( ( A e. RR /\ B e. RR ) /\ ( 0 <_ A /\ A <_ B ) ) /\ ( ( C e. RR /\ D e. RR ) /\ ( 0 < C /\ C <_ D ) ) ) -> ( A / D ) <_ ( B / C ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cC
    cr
    wcel
    #
    cD
    cr
    wcel
    #
    wa
    #
    cc0
    cC
    clt
    wbr
    #
    cC
    cD
    cle
    wbr
    #
    wa
    #
    wa
    #
    wa
    cA
    c1
    cD
    cdiv
    co
    #
    cmul
    co
    #
    cB
    c1
    cC
    cdiv
    co
    #
    cmul
    co
    #
    cA
    cD
    cdiv
    co
    #
    cB
    cC
    cdiv
    co
    #
    cle
    @13
    @6
    @14
    cr
    wcel
    #
    @16
    cr
    wcel
    #
    wa
    #
    cc0
    @14
    cle
    wbr
    #
    @14
    @16
    cle
    wbr
    #
    wa
    #
    wa
    #
    @15
    @17
    cle
    wbr
    #
    @13
    @20
    @21
    @25
    @13
    cD
    @7
    @8
    @12
    simplr
    #
    @13
    cD
    @9
    @12
    cc0
    cD
    clt
    wbr
    #
    cc0
    cr
    wcel
    #
    @7
    @8
    @12
    @29
    wi
    0re
    cc0
    cC
    cD
    ltletr
    mp3an1
    imp
    #
    gt0ne0d
    #
    rereccld
    #
    @7
    @10
    @21
    @8
    @11
    @7
    @10
    cC
    cc0
    wne
    #
    @21
    cC
    gt0ne0
    #
    cC
    rereccl
    syldan
    ad2ant2r
    @13
    @23
    @24
    @13
    cc0
    @14
    clt
    wbr
    #
    @23
    @13
    @8
    @29
    @36
    @28
    @31
    cD
    recgt0
    syl2anc
    @13
    @30
    @20
    @36
    @23
    wi
    0re
    @33
    cc0
    @14
    ltle
    sylancr
    mpd
    @13
    @11
    @24
    @9
    @10
    @11
    simprr
    @13
    @7
    @10
    wa
    #
    @8
    @29
    @11
    @24
    wb
    @7
    @10
    @37
    @8
    @11
    @37
    id
    ad2ant2r
    @28
    @31
    cC
    cD
    lerec
    syl12anc
    mpbid
    jca
    jca31
    @6
    @26
    wa
    #
    @0
    @3
    wa
    @1
    wa
    #
    @20
    @23
    wa
    #
    @21
    wa
    wa
    @4
    @24
    wa
    @27
    @38
    @39
    @40
    @21
    @38
    @0
    @3
    @1
    @0
    @1
    @5
    @26
    simplll
    @2
    @3
    @4
    @26
    simplrl
    @0
    @1
    @5
    @26
    simpllr
    jca31
    @38
    @20
    @23
    @6
    @20
    @21
    @25
    simprll
    @6
    @22
    @23
    @24
    simprrl
    jca
    @6
    @20
    @21
    @25
    simprlr
    jca32
    @38
    @4
    @24
    @2
    @3
    @4
    @26
    simplrr
    @6
    @22
    @23
    @24
    simprrr
    jca
    cA
    cB
    @14
    @16
    lemul12a
    sylc
    sylan2
    @2
    @13
    @18
    @15
    wceq
    #
    @5
    @0
    @13
    @41
    @1
    @0
    @13
    wa
    cA
    cD
    @0
    cA
    cc
    wcel
    @13
    cA
    recn
    adantr
    @13
    cD
    cc
    wcel
    #
    @0
    @8
    @42
    @7
    @12
    cD
    recn
    ad2antlr
    adantl
    @13
    cD
    cc0
    wne
    @0
    @32
    adantl
    divrecd
    adantlr
    adantlr
    @2
    @13
    @19
    @17
    wceq
    #
    @5
    @1
    @13
    @43
    @0
    @1
    @7
    @12
    @43
    @8
    @1
    @7
    @10
    @43
    @11
    @1
    @37
    wa
    cB
    cC
    @1
    cB
    cc
    wcel
    @37
    cB
    recn
    adantr
    @7
    cC
    cc
    wcel
    @1
    @10
    cC
    recn
    ad2antrl
    @37
    @34
    @1
    @35
    adantl
    divrecd
    adantrrr
    adantrlr
    adantll
    adantlr
    3brtr4d
end
