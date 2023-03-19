include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "crp.mm"
include "wral.mm"
include "wa.mm"
include "nfv.mm"
include "nfan.mm"
include "wcel.mm"
include "cxr.mm"
include "ad2antrr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "icossxr.mm"
include "sseldi.mm"
include "1red.mm"
include "cr.mm"
include "rpre.mm"
include "adantl.mm"
include "readdcld.mm"
include "rge0ssre.mm"
include "adantr.mm"
include "remulcld.mm"
include "rexrd.mm"
include "adantlr.mm"
include "simplr.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "id.mm"
include "icogelb.mm"
include "syl3anc.mm"
include "syl.mm"
include "ltaddrpd.mm"
include "ltled.mm"
include "lemulge12d.mm"
include "xrletrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "wceq.mm"
include "ad3antrrr.mm"
include "0red.mm"
include "eqeltrd.mm"
include "adantll.mm"
include "c2.mm"
include "1rp.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "1p1e2.mm"
include "breqtrd.mm"
include "simpr.mm"
include "simpl.mm"
include "2cnd.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "ad4ant24.mm"
include "clt.mm"
include "rpgt0.mm"
include "oveq1.mm"
include "cc.mm"
include "recnd.mm"
include "addid2d.mm"
include "eqtr2d.mm"
include "xrlelttrd.mm"
include "xrltled.mm"
include "wn.mm"
include "wne.mm"
include "necon3bi.mm"
include "leneltd.mm"
include "elrpd.mm"
include "ad4ant14.mm"
include "cdiv.mm"
include "rpdivcld.mm"
include "simpll.mm"
include "adantlll.mm"
include "1cnd.mm"
include "rpcn.mm"
include "rpne0.mm"
include "divcld.mm"
include "adddird.mm"
include "mulid2d.mm"
include "divcan1d.mm"
include "oveq12d.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "pm2.61dan.mm"
include "ralrimiva.mm"
include "wb.mm"
include "xralrple.mm"
include "mpbird.mm"
include "impbid.mm"

theorem xralrple2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume xralrple2.x: |- F/ x ph
  assume xralrple2.a: |- ( ph -> A e. RR* )
  assume xralrple2.b: |- ( ph -> B e. ( 0 [,) +oo ) )

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint ph y
  assert |- ( ph -> ( A <_ B <-> A. x e. RR+ A <_ ( ( 1 + x ) x. B ) ) )

  proof
    wph
    cA
    cB
    cle
    wbr
    #
    cA
    c1
    vx
    cv
    #
    caddc
    co
    #
    cB
    cmul
    co
    #
    cle
    wbr
    #
    vx
    crp
    wral
    #
    wph
    @0
    @5
    wph
    @0
    wa
    #
    @4
    vx
    crp
    wph
    @0
    vx
    xralrple2.x
    @0
    vx
    nfv
    nfan
    @6
    @1
    crp
    wcel
    #
    @4
    @6
    @7
    wa
    #
    cA
    cB
    @3
    wph
    cA
    cxr
    wcel
    #
    @0
    @7
    xralrple2.a
    ad2antrr
    @8
    cc0
    cpnf
    cico
    co
    #
    cxr
    cB
    cc0
    cpnf
    icossxr
    wph
    cB
    @10
    wcel
    #
    @0
    @7
    xralrple2.b
    ad2antrr
    sseldi
    wph
    @7
    @3
    cxr
    wcel
    @0
    wph
    @7
    wa
    #
    @3
    @12
    @2
    cB
    @12
    c1
    @1
    @12
    1red
    @7
    @1
    cr
    wcel
    wph
    @1
    rpre
    #
    adantl
    readdcld
    wph
    cB
    cr
    wcel
    #
    @7
    wph
    @10
    cr
    cB
    rge0ssre
    xralrple2.b
    sseldi
    #
    adantr
    remulcld
    rexrd
    adantlr
    wph
    @0
    @7
    simplr
    @8
    cB
    @2
    wph
    @14
    @0
    @7
    @15
    ad2antrr
    @7
    @2
    cr
    wcel
    @6
    @7
    c1
    @1
    @7
    1red
    #
    @13
    readdcld
    #
    adantl
    wph
    cc0
    cB
    cle
    wbr
    #
    @0
    @7
    wph
    @11
    @18
    xralrple2.b
    @11
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @11
    @18
    @19
    @11
    0xr
    a1i
    @20
    @11
    pnfxr
    a1i
    @11
    id
    cc0
    cpnf
    cB
    icogelb
    syl3anc
    syl
    #
    ad2antrr
    @7
    c1
    @2
    cle
    wbr
    @6
    @7
    c1
    @2
    @16
    @17
    @7
    c1
    @1
    @16
    @7
    id
    ltaddrpd
    ltled
    adantl
    lemulge12d
    xrletrd
    ex
    ralrimi
    ex
    wph
    @5
    @0
    wph
    @5
    wa
    #
    @0
    cA
    cB
    vy
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    crp
    wral
    #
    @22
    @25
    vy
    crp
    @22
    @23
    crp
    wcel
    #
    wa
    #
    cB
    cc0
    wceq
    #
    @25
    @28
    @29
    wa
    #
    cA
    @24
    wph
    @9
    @5
    @27
    @29
    xralrple2.a
    ad3antrrr
    #
    @27
    @29
    @24
    cxr
    wcel
    @22
    @27
    @29
    wa
    #
    @24
    @32
    cB
    @23
    @29
    @14
    @27
    @29
    cB
    cc0
    cr
    @29
    id
    #
    @29
    0red
    eqeltrd
    adantl
    @27
    @23
    cr
    wcel
    @29
    @23
    rpre
    #
    adantr
    readdcld
    rexrd
    adantll
    #
    @30
    cA
    cc0
    @24
    @31
    @19
    @30
    0xr
    a1i
    @35
    @5
    @29
    cA
    cc0
    cle
    wbr
    #
    wph
    @27
    @5
    @29
    wa
    cA
    c2
    cB
    cmul
    co
    #
    cle
    wbr
    #
    @29
    @36
    @5
    @38
    @29
    @5
    cA
    c1
    c1
    caddc
    co
    #
    cB
    cmul
    co
    #
    @37
    cle
    @5
    c1
    crp
    wcel
    #
    @5
    cA
    @40
    cle
    wbr
    #
    @41
    @5
    1rp
    a1i
    @5
    id
    @4
    @42
    vx
    c1
    crp
    @1
    c1
    wceq
    #
    @3
    @40
    cA
    cle
    @43
    @2
    @39
    cB
    cmul
    @1
    c1
    c1
    caddc
    oveq2
    oveq1d
    breq2d
    rspcva
    syl2anc
    @5
    @39
    c2
    cB
    cmul
    @39
    c2
    wceq
    @5
    1p1e2
    a1i
    oveq1d
    breqtrd
    adantr
    @5
    @29
    simpr
    @38
    @29
    wa
    cA
    @37
    cc0
    cle
    @38
    @29
    simpl
    @29
    @37
    cc0
    wceq
    @38
    @29
    @37
    c2
    cc0
    cmul
    co
    cc0
    cB
    cc0
    c2
    cmul
    oveq2
    @29
    c2
    @29
    2cnd
    mul01d
    eqtrd
    adantl
    breqtrd
    syl2anc
    ad4ant24
    @27
    @29
    cc0
    @24
    clt
    wbr
    @22
    @32
    cc0
    @23
    @24
    clt
    @27
    cc0
    @23
    clt
    wbr
    @29
    @23
    rpgt0
    adantr
    @32
    @24
    cc0
    @23
    caddc
    co
    #
    @23
    @29
    @24
    @44
    wceq
    @27
    cB
    cc0
    @23
    caddc
    oveq1
    adantl
    @32
    @23
    @27
    @23
    cc
    wcel
    #
    @29
    @27
    @23
    @34
    recnd
    #
    adantr
    addid2d
    eqtr2d
    breqtrd
    adantll
    xrlelttrd
    xrltled
    @28
    @29
    wn
    #
    wa
    @28
    cB
    crp
    wcel
    #
    @25
    @28
    @47
    simpl
    wph
    @47
    @48
    @5
    @27
    wph
    @47
    wa
    #
    cB
    wph
    @14
    @47
    @15
    adantr
    #
    @49
    cc0
    cB
    @49
    0red
    @50
    wph
    @18
    @47
    @21
    adantr
    @47
    cB
    cc0
    wne
    #
    wph
    @29
    cB
    cc0
    @33
    necon3bi
    adantl
    leneltd
    elrpd
    ad4ant14
    @28
    @48
    wa
    cA
    c1
    @23
    cB
    cdiv
    co
    #
    caddc
    co
    #
    cB
    cmul
    co
    #
    @24
    cle
    @5
    @27
    @48
    cA
    @54
    cle
    wbr
    #
    wph
    @5
    @27
    wa
    #
    @48
    wa
    #
    @52
    crp
    wcel
    @5
    @55
    @57
    @23
    cB
    @5
    @27
    @48
    simplr
    @56
    @48
    simpr
    rpdivcld
    @5
    @27
    @48
    simpll
    @4
    @55
    vx
    @52
    crp
    @1
    @52
    wceq
    #
    @3
    @54
    cA
    cle
    @58
    @2
    @53
    cB
    cmul
    @1
    @52
    c1
    caddc
    oveq2
    oveq1d
    breq2d
    rspcva
    syl2anc
    adantlll
    @27
    @48
    @54
    @24
    wceq
    @22
    @27
    @48
    wa
    #
    @54
    c1
    cB
    cmul
    co
    #
    @52
    cB
    cmul
    co
    #
    caddc
    co
    @24
    @24
    @59
    c1
    @52
    cB
    @59
    1cnd
    @59
    @23
    cB
    @27
    @45
    @48
    @46
    adantr
    #
    @48
    cB
    cc
    wcel
    @27
    cB
    rpcn
    adantl
    #
    @48
    @51
    @27
    cB
    rpne0
    adantl
    #
    divcld
    @63
    adddird
    @59
    @60
    cB
    @61
    @23
    caddc
    @59
    cB
    @63
    mulid2d
    @59
    @23
    cB
    @62
    @63
    @64
    divcan1d
    oveq12d
    @59
    @24
    eqidd
    3eqtrd
    adantll
    breqtrd
    syl2anc
    pm2.61dan
    ralrimiva
    wph
    @0
    @26
    wb
    #
    @5
    wph
    @9
    @14
    @65
    xralrple2.a
    @15
    vy
    cA
    cB
    xralrple
    syl2anc
    adantr
    mpbird
    ex
    impbid
end
