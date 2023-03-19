include "wcel.mm"
include "c0.mm"
include "cpr.mm"
include "csalg.mm"
include "cuni.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "w3a.mm"
include "0ex.mm"
include "prid1.mm"
include "a1i.mm"
include "wa.mm"
include "wceq.mm"
include "cun.mm"
include "cvv.mm"
include "id.mm"
include "uniprg.mm"
include "syl2anc.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "difeq1d.mm"
include "adantr.mm"
include "difeq2.mm"
include "adantl.mm"
include "dif0.mm"
include "eqtrd.mm"
include "prid2g.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "wn.mm"
include "simpll.mm"
include "wne.mm"
include "simpl.mm"
include "neqne.mm"
include "elprn1.mm"
include "adantll.mm"
include "difid.mm"
include "pm2.61dan.mm"
include "ralrimiva.mm"
include "wss.mm"
include "elpwi.mm"
include "uniss.mm"
include "syl.mm"
include "sseqtrd.mm"
include "elssuni.mm"
include "jca.mm"
include "eqss.mm"
include "sylibr.mm"
include "ad2antrr.mm"
include "csn.mm"
include "pwpr.mm"
include "syl6eleq.mm"
include "snidg.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "necon3bi.mm"
include "simplr.mm"
include "pm2.65da.mm"
include "elunnel2.mm"
include "unieq.mm"
include "uni0.mm"
include "unisn.mm"
include "a1d.mm"
include "3jca.mm"
include "wb.mm"
include "prex.mm"
include "issal.mm"
include "mpbird.mm"

theorem prsal
  let cV: class V
  let cX: class X
  let vy: setvar y
  let vk: setvar k
  let vx: setvar x


  assert |- ( X e. V -> { (/) , X } e. SAlg )

  proof
    cX
    cV
    wcel
    #
    c0
    cX
    cpr
    #
    csalg
    wcel
    #
    c0
    @1
    wcel
    #
    @1
    cuni
    #
    vy
    cv
    #
    cdif
    #
    @1
    wcel
    #
    vy
    @1
    wral
    #
    @5
    com
    cdom
    wbr
    #
    @5
    cuni
    #
    @1
    wcel
    #
    wi
    #
    vy
    @1
    cpw
    #
    wral
    #
    w3a
    #
    @0
    @3
    @8
    @14
    @3
    @0
    c0
    cX
    0ex
    prid1
    #
    a1i
    @0
    @7
    vy
    @1
    @0
    @5
    @1
    wcel
    #
    wa
    #
    @6
    cX
    @5
    cdif
    #
    @1
    @0
    @6
    @19
    wceq
    @17
    @0
    @4
    cX
    @5
    @0
    @4
    c0
    cX
    cun
    #
    cX
    cX
    @0
    c0
    cvv
    wcel
    #
    @0
    @4
    @20
    wceq
    @21
    @0
    0ex
    a1i
    @0
    id
    #
    c0
    cX
    cvv
    cV
    uniprg
    syl2anc
    @20
    cX
    wceq
    @0
    @20
    cX
    c0
    cun
    cX
    c0
    cX
    uncom
    cX
    un0
    eqtri
    a1i
    @0
    cX
    eqidd
    3eqtrd
    #
    difeq1d
    adantr
    @18
    @5
    c0
    wceq
    #
    @19
    @1
    wcel
    #
    @0
    @24
    @25
    @17
    @0
    @24
    wa
    #
    @19
    cX
    @1
    @26
    @19
    cX
    c0
    cdif
    #
    cX
    @24
    @19
    @27
    wceq
    @0
    @5
    c0
    cX
    difeq2
    adantl
    @27
    cX
    wceq
    @26
    cX
    dif0
    a1i
    eqtrd
    @0
    cX
    @1
    wcel
    #
    @24
    c0
    cX
    cV
    prid2g
    #
    adantr
    eqeltrd
    adantlr
    @18
    @24
    wn
    #
    wa
    @0
    @5
    cX
    wceq
    #
    @25
    @0
    @17
    @30
    simpll
    @17
    @30
    @31
    @0
    @17
    @30
    wa
    @17
    @5
    c0
    wne
    #
    @31
    @17
    @30
    simpl
    @30
    @32
    @17
    @5
    c0
    neqne
    #
    adantl
    @5
    c0
    cX
    elprn1
    syl2anc
    adantll
    @31
    @25
    @0
    @31
    @19
    c0
    @1
    @31
    @19
    cX
    cX
    cdif
    #
    c0
    @5
    cX
    cX
    difeq2
    @34
    c0
    wceq
    @31
    cX
    difid
    a1i
    eqtrd
    @3
    @31
    @16
    a1i
    eqeltrd
    adantl
    syl2anc
    pm2.61dan
    eqeltrd
    ralrimiva
    @0
    @12
    vy
    @13
    @0
    @5
    @13
    wcel
    #
    wa
    #
    @11
    @9
    @36
    cX
    @5
    wcel
    #
    @11
    @36
    @37
    wa
    #
    @10
    cX
    @1
    @38
    @10
    cX
    wss
    #
    cX
    @10
    wss
    #
    wa
    @10
    cX
    wceq
    @38
    @39
    @40
    @36
    @39
    @37
    @36
    @10
    @4
    cX
    @35
    @10
    @4
    wss
    #
    @0
    @35
    @5
    @1
    wss
    @41
    @5
    @1
    elpwi
    @5
    @1
    uniss
    syl
    adantl
    @0
    @4
    cX
    wceq
    @35
    @23
    adantr
    sseqtrd
    adantr
    @37
    @40
    @36
    cX
    @5
    elssuni
    adantl
    jca
    @10
    cX
    eqss
    sylibr
    @0
    @28
    @35
    @37
    @29
    ad2antrr
    eqeltrd
    @36
    @37
    wn
    #
    wa
    #
    @10
    c0
    @1
    @43
    @5
    c0
    c0
    csn
    #
    cpr
    #
    wcel
    #
    @10
    c0
    wceq
    #
    @43
    @5
    @45
    cX
    csn
    #
    @1
    cpr
    #
    cun
    #
    wcel
    #
    @5
    @49
    wcel
    #
    wn
    #
    @46
    @35
    @42
    @51
    @0
    @35
    @51
    @42
    @35
    @5
    @13
    @50
    @35
    id
    c0
    cX
    pwpr
    syl6eleq
    adantr
    adantll
    @0
    @42
    @53
    @35
    @0
    @42
    wa
    @52
    @37
    @0
    @52
    @37
    @42
    @0
    @52
    wa
    #
    @5
    @48
    wceq
    #
    @37
    @0
    @55
    @37
    @52
    @0
    @55
    wa
    cX
    @48
    @5
    @0
    cX
    @48
    wcel
    @55
    cX
    cV
    snidg
    adantr
    @55
    @48
    @5
    wceq
    @0
    @55
    @5
    @48
    @55
    id
    #
    eqcomd
    adantl
    eleqtrd
    adantlr
    @54
    @55
    wn
    #
    wa
    @0
    @5
    @1
    wceq
    #
    @37
    @0
    @0
    @52
    @57
    @22
    ad2antrr
    @52
    @57
    @58
    @0
    @52
    @57
    wa
    @52
    @5
    @48
    wne
    #
    @58
    @52
    @57
    simpl
    @57
    @59
    @52
    @55
    @5
    @48
    @56
    necon3bi
    adantl
    @5
    @48
    @1
    elprn1
    syl2anc
    adantll
    @0
    @58
    wa
    cX
    @1
    @5
    @0
    @28
    @58
    @29
    adantr
    @58
    @1
    @5
    wceq
    @0
    @58
    @5
    @1
    @58
    id
    eqcomd
    adantl
    eleqtrd
    syl2anc
    pm2.61dan
    adantlr
    @0
    @42
    @52
    simplr
    pm2.65da
    adantlr
    @5
    @45
    @49
    elunnel2
    syl2anc
    @46
    @24
    @47
    @24
    @47
    @46
    @24
    @10
    c0
    cuni
    #
    c0
    @5
    c0
    unieq
    @60
    c0
    wceq
    @24
    uni0
    a1i
    eqtrd
    adantl
    @46
    @30
    wa
    #
    @5
    @44
    wceq
    #
    @47
    @61
    @46
    @32
    @62
    @46
    @30
    simpl
    @30
    @32
    @46
    @33
    adantl
    @5
    c0
    @44
    elprn1
    syl2anc
    @62
    @10
    @44
    cuni
    #
    c0
    @5
    @44
    unieq
    @63
    c0
    wceq
    @62
    c0
    0ex
    unisn
    a1i
    eqtrd
    syl
    pm2.61dan
    syl
    @3
    @43
    @16
    a1i
    eqeltrd
    pm2.61dan
    a1d
    ralrimiva
    3jca
    @0
    @1
    cvv
    wcel
    #
    @2
    @15
    wb
    @64
    @0
    c0
    cX
    prex
    a1i
    vy
    @1
    cvv
    issal
    syl
    mpbird
end
