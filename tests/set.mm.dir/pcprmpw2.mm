include "cprime.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn0.mm"
include "wrex.mm"
include "cpc.mm"
include "wceq.mm"
include "simplr.mm"
include "nnnn0d.mm"
include "prmnn.mm"
include "ad2antrr.mm"
include "pccl.mm"
include "adantr.mm"
include "nnexpcld.mm"
include "cle.mm"
include "wral.mm"
include "nn0red.mm"
include "leidd.mm"
include "cz.mm"
include "simpll.mm"
include "nn0zd.mm"
include "pcid.mm"
include "syl2anc.mm"
include "breqtrrd.mm"
include "simpr.mm"
include "oveq1d.mm"
include "3brtr4d.mm"
include "wne.mm"
include "cc0.mm"
include "wn.mm"
include "simplrr.mm"
include "wi.mm"
include "prmz.mm"
include "adantl.mm"
include "nnzd.mm"
include "simprl.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "simplrl.mm"
include "prmdvdsexpr.mm"
include "syld.mm"
include "necon3ad.mm"
include "imp.mm"
include "wb.mm"
include "pceq0.mm"
include "mpbird.mm"
include "pccld.mm"
include "nn0ge0d.mm"
include "eqbrtrd.mm"
include "pm2.61dane.mm"
include "ralrimiva.mm"
include "pc2dvds.mm"
include "pcdvds.mm"
include "dvdseq.mm"
include "syl22anc.mm"
include "rexlimdvaa.mm"
include "iddvds.mm"
include "syl.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rspcev.mm"
include "breq1.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem pcprmpw2
  let cA: class A
  let cP: class P
  let vn: setvar n
  let vp: setvar p

  disjoint A n
  disjoint P n
  disjoint n p
  disjoint A p
  disjoint P p
  assert |- ( ( P e. Prime /\ A e. NN ) -> ( E. n e. NN0 A || ( P ^ n ) <-> A = ( P ^ ( P pCnt A ) ) ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    cn
    wcel
    #
    wa
    #
    cA
    cP
    vn
    cv
    #
    cexp
    co
    #
    cdvds
    wbr
    #
    vn
    cn0
    wrex
    #
    cA
    cP
    cP
    cA
    cpc
    co
    #
    cexp
    co
    #
    wceq
    #
    @2
    @5
    @9
    vn
    cn0
    @2
    @3
    cn0
    wcel
    #
    @5
    wa
    #
    wa
    #
    cA
    cn0
    wcel
    @8
    cn0
    wcel
    cA
    @8
    cdvds
    wbr
    #
    @8
    cA
    cdvds
    wbr
    #
    @9
    @12
    cA
    @0
    @1
    @11
    simplr
    #
    nnnn0d
    @12
    @8
    @12
    cP
    @7
    @0
    cP
    cn
    wcel
    #
    @1
    @11
    cP
    prmnn
    #
    ad2antrr
    #
    @2
    @7
    cn0
    wcel
    #
    @11
    cP
    cA
    pccl
    #
    adantr
    #
    nnexpcld
    #
    nnnn0d
    @12
    @13
    vp
    cv
    #
    cA
    cpc
    co
    #
    @23
    @8
    cpc
    co
    #
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @12
    @26
    vp
    cprime
    @12
    @23
    cprime
    wcel
    #
    wa
    #
    @26
    @23
    cP
    @29
    @23
    cP
    wceq
    #
    wa
    #
    @7
    cP
    @8
    cpc
    co
    #
    @24
    @25
    cle
    @12
    @7
    @32
    cle
    wbr
    @28
    @30
    @12
    @7
    @7
    @32
    cle
    @12
    @7
    @12
    @7
    @21
    nn0red
    leidd
    @12
    @0
    @7
    cz
    wcel
    @32
    @7
    wceq
    @0
    @1
    @11
    simpll
    #
    @12
    @7
    @21
    nn0zd
    @7
    cP
    pcid
    syl2anc
    breqtrrd
    ad2antrr
    @31
    @23
    cP
    cA
    cpc
    @29
    @30
    simpr
    #
    oveq1d
    @31
    @23
    cP
    @8
    cpc
    @34
    oveq1d
    3brtr4d
    @29
    @23
    cP
    wne
    #
    wa
    #
    @24
    cc0
    @25
    cle
    @36
    @24
    cc0
    wceq
    #
    @23
    cA
    cdvds
    wbr
    #
    wn
    #
    @29
    @35
    @39
    @29
    @38
    @23
    cP
    @29
    @38
    @23
    @4
    cdvds
    wbr
    #
    @30
    @29
    @38
    @5
    @40
    @2
    @10
    @5
    @28
    simplrr
    @29
    @23
    cz
    wcel
    #
    cA
    cz
    wcel
    #
    @4
    cz
    wcel
    @38
    @5
    wa
    @40
    wi
    @28
    @41
    @12
    @23
    prmz
    adantl
    @29
    cA
    @12
    @1
    @28
    @15
    adantr
    nnzd
    @29
    @4
    @12
    @4
    cn
    wcel
    @28
    @12
    cP
    @3
    @18
    @2
    @10
    @5
    simprl
    nnexpcld
    adantr
    nnzd
    @23
    cA
    @4
    dvdstr
    syl3anc
    mpan2d
    @29
    @28
    @0
    @10
    @40
    @30
    wi
    @12
    @28
    simpr
    @12
    @0
    @28
    @33
    adantr
    @2
    @10
    @5
    @28
    simplrl
    @23
    cP
    @3
    prmdvdsexpr
    syl3anc
    syld
    necon3ad
    imp
    @36
    @28
    @1
    @37
    @39
    wb
    @12
    @28
    @35
    simplr
    #
    @12
    @1
    @28
    @35
    @15
    ad2antrr
    @23
    cA
    pceq0
    syl2anc
    mpbird
    @36
    @25
    @36
    @23
    @8
    @43
    @12
    @8
    cn
    wcel
    @28
    @35
    @22
    ad2antrr
    pccld
    nn0ge0d
    eqbrtrd
    pm2.61dane
    ralrimiva
    @12
    @42
    @8
    cz
    wcel
    #
    @13
    @27
    wb
    @12
    cA
    @15
    nnzd
    @12
    @8
    @22
    nnzd
    cA
    @8
    vp
    pc2dvds
    syl2anc
    mpbird
    @2
    @14
    @11
    cP
    cA
    pcdvds
    adantr
    cA
    @8
    dvdseq
    syl22anc
    rexlimdvaa
    @2
    @6
    @9
    @8
    @4
    cdvds
    wbr
    #
    vn
    cn0
    wrex
    #
    @2
    @19
    @8
    @8
    cdvds
    wbr
    #
    @46
    @20
    @2
    @44
    @47
    @2
    @8
    @2
    cP
    @7
    @0
    @16
    @1
    @17
    adantr
    @20
    nnexpcld
    nnzd
    @8
    iddvds
    syl
    @45
    @47
    vn
    @7
    cn0
    @3
    @7
    wceq
    @4
    @8
    @8
    cdvds
    @3
    @7
    cP
    cexp
    oveq2
    breq2d
    rspcev
    syl2anc
    @9
    @5
    @45
    vn
    cn0
    cA
    @8
    @4
    cdvds
    breq1
    rexbidv
    syl5ibrcom
    impbid
end
