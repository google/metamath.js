include "c4.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cgbe.mm"
include "wcel.mm"
include "wi.mm"
include "ceven.mm"
include "wral.mm"
include "c5.mm"
include "cgbow.mm"
include "codd.mm"
include "cz.mm"
include "oddz.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "5nn.mm"
include "nnzi.mm"
include "zltp1le.mm"
include "mpan.mm"
include "c6.mm"
include "wceq.mm"
include "wo.mm"
include "5p1e6.mm"
include "breq1i.mm"
include "cr.mm"
include "6re.mm"
include "a1i.mm"
include "zre.mm"
include "leloed.mm"
include "syl5bb.mm"
include "6nn.mm"
include "c7.mm"
include "6p1e7.mm"
include "7re.mm"
include "wa.mm"
include "c3.mm"
include "cmin.mm"
include "simpr.mm"
include "3odd.mm"
include "jctir.mm"
include "omoeALTV.mm"
include "breq2.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "3syl.mm"
include "4p3e7.mm"
include "eqcomi.mm"
include "4re.mm"
include "3re.mm"
include "w3a.mm"
include "ltaddsub.mm"
include "biimpd.mm"
include "syl3anc.mm"
include "syl5bi.mm"
include "impcom.mm"
include "adantr.mm"
include "pm2.27.mm"
include "syl.mm"
include "cprime.mm"
include "wrex.mm"
include "isgbe.mm"
include "3prm.mm"
include "cc.mm"
include "zcn.mm"
include "3cn.mm"
include "npcan.mm"
include "eqcomd.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "sylan9eq.mm"
include "rspcedeq2vd.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "syl5ib.mm"
include "3ad2ant3.mm"
include "com12.mm"
include "ad4antlr.mm"
include "reximdva.mm"
include "jctild.mm"
include "isgbow.mm"
include "syl6ibr.mm"
include "adantld.mm"
include "3syld.mm"
include "ex.mm"
include "com23.mm"
include "7gbow.mm"
include "mpbii.mm"
include "a1d.mm"
include "jaoi.mm"
include "sylbid.mm"
include "6even.mm"
include "evennodd.mm"
include "pm2.21d.mm"
include "ax-mp.mm"
include "syl6bir.mm"
include "com24.mm"
include "mpcom.mm"
include "ralrimiva.mm"

theorem sbgoldbwt
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vk: setvar k
  let vx: setvar x

  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint k x
  assert |- ( A. n e. Even ( 4 < n -> n e. GoldbachEven ) -> A. m e. Odd ( 5 < m -> m e. GoldbachOddW ) )

  proof
    c4
    vn
    cv
    #
    clt
    wbr
    #
    @0
    cgbe
    wcel
    #
    wi
    #
    vn
    ceven
    wral
    #
    c5
    vm
    cv
    #
    clt
    wbr
    #
    @5
    cgbow
    wcel
    #
    wi
    #
    vm
    codd
    @5
    codd
    wcel
    #
    @4
    @8
    @5
    cz
    wcel
    #
    @9
    @4
    @8
    wi
    @5
    oddz
    @10
    @6
    @4
    @9
    @7
    @10
    @6
    c5
    c1
    caddc
    co
    #
    @5
    cle
    wbr
    #
    @4
    @9
    @7
    wi
    #
    wi
    #
    c5
    cz
    wcel
    @10
    @6
    @12
    wb
    c5
    5nn
    nnzi
    c5
    @5
    zltp1le
    mpan
    @10
    @12
    c6
    @5
    clt
    wbr
    #
    c6
    @5
    wceq
    #
    wo
    #
    @14
    @12
    c6
    @5
    cle
    wbr
    @10
    @17
    @11
    c6
    @5
    cle
    5p1e6
    breq1i
    @10
    c6
    @5
    c6
    cr
    wcel
    @10
    6re
    a1i
    @5
    zre
    #
    leloed
    syl5bb
    @17
    @10
    @14
    @15
    @10
    @14
    wi
    #
    @16
    @10
    @15
    @14
    @10
    @15
    c6
    c1
    caddc
    co
    #
    @5
    cle
    wbr
    #
    @14
    c6
    cz
    wcel
    @10
    @15
    @21
    wb
    c6
    6nn
    nnzi
    c6
    @5
    zltp1le
    mpan
    @10
    @21
    c7
    @5
    clt
    wbr
    #
    c7
    @5
    wceq
    #
    wo
    #
    @14
    @21
    c7
    @5
    cle
    wbr
    @10
    @24
    @20
    c7
    @5
    cle
    6p1e7
    breq1i
    @10
    c7
    @5
    c7
    cr
    wcel
    @10
    7re
    a1i
    @18
    leloed
    syl5bb
    @24
    @10
    @14
    @22
    @19
    @23
    @22
    @10
    @14
    @22
    @10
    wa
    #
    @9
    @4
    @7
    @25
    @9
    @4
    @7
    wi
    @25
    @9
    wa
    #
    @4
    c4
    @5
    c3
    cmin
    co
    #
    clt
    wbr
    #
    @27
    cgbe
    wcel
    #
    wi
    #
    @29
    @7
    @26
    @9
    c3
    codd
    wcel
    #
    wa
    @27
    ceven
    wcel
    #
    @4
    @30
    wi
    @26
    @9
    @31
    @25
    @9
    simpr
    #
    3odd
    jctir
    @5
    c3
    omoeALTV
    @3
    @30
    vn
    @27
    ceven
    @0
    @27
    wceq
    @1
    @28
    @2
    @29
    @0
    @27
    c4
    clt
    breq2
    @0
    @27
    cgbe
    eleq1
    imbi12d
    rspcv
    3syl
    @26
    @28
    @30
    @29
    wi
    @25
    @28
    @9
    @10
    @22
    @28
    @22
    c4
    c3
    caddc
    co
    #
    @5
    clt
    wbr
    #
    @10
    @28
    c7
    @34
    @5
    clt
    @34
    c7
    4p3e7
    eqcomi
    breq1i
    @10
    c4
    cr
    wcel
    #
    c3
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @35
    @28
    wi
    @36
    @10
    4re
    a1i
    @37
    @10
    3re
    a1i
    @18
    @36
    @37
    @38
    w3a
    @35
    @28
    c4
    c3
    @5
    ltaddsub
    biimpd
    syl3anc
    syl5bi
    impcom
    adantr
    @28
    @29
    pm2.27
    syl
    @29
    @32
    vp
    cv
    #
    codd
    wcel
    #
    vq
    cv
    #
    codd
    wcel
    #
    @27
    @39
    @41
    caddc
    co
    #
    wceq
    #
    w3a
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wa
    @26
    @7
    @27
    vq
    vp
    isgbe
    @26
    @47
    @7
    @32
    @26
    @47
    @9
    @5
    @43
    vr
    cv
    #
    caddc
    co
    #
    wceq
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wa
    @7
    @26
    @47
    @53
    @9
    @26
    @46
    @52
    vp
    cprime
    @26
    @39
    cprime
    wcel
    #
    wa
    @45
    @51
    vq
    cprime
    @10
    @45
    @51
    wi
    @22
    @9
    @54
    @41
    cprime
    wcel
    @45
    @10
    @51
    @44
    @40
    @10
    @51
    wi
    @42
    @10
    @5
    @27
    @48
    caddc
    co
    #
    wceq
    #
    vr
    cprime
    wrex
    @44
    @51
    @10
    vr
    c3
    cprime
    @5
    @55
    c3
    cprime
    wcel
    @10
    3prm
    a1i
    @10
    @48
    c3
    wceq
    @5
    @27
    c3
    caddc
    co
    #
    @55
    @10
    @5
    cc
    wcel
    #
    c3
    cc
    wcel
    #
    wa
    #
    @5
    @57
    wceq
    @10
    @58
    @59
    @5
    zcn
    3cn
    jctir
    @60
    @57
    @5
    @5
    c3
    npcan
    eqcomd
    syl
    @57
    @55
    wceq
    c3
    @48
    c3
    @48
    @27
    caddc
    oveq2
    eqcoms
    sylan9eq
    rspcedeq2vd
    @44
    @56
    @50
    vr
    cprime
    @44
    @55
    @49
    @5
    @27
    @43
    @48
    caddc
    oveq1
    eqeq2d
    rexbidv
    syl5ib
    3ad2ant3
    com12
    ad4antlr
    reximdva
    reximdva
    @33
    jctild
    @5
    vr
    vq
    vp
    isgbow
    syl6ibr
    adantld
    syl5bi
    3syld
    ex
    com23
    ex
    @23
    @14
    @10
    @23
    @13
    @4
    @23
    @7
    @9
    @23
    c7
    cgbow
    wcel
    @7
    7gbow
    c7
    @5
    cgbow
    eleq1
    mpbii
    a1d
    a1d
    a1d
    jaoi
    com12
    sylbid
    sylbid
    com12
    @16
    @14
    @10
    @16
    @13
    @4
    @16
    @9
    c6
    codd
    wcel
    #
    @7
    c6
    @5
    codd
    eleq1
    c6
    ceven
    wcel
    #
    @61
    @7
    wi
    6even
    @62
    @61
    @7
    c6
    evennodd
    pm2.21d
    ax-mp
    syl6bir
    a1d
    a1d
    jaoi
    com12
    sylbid
    sylbid
    com24
    mpcom
    impcom
    ralrimiva
end
