include "cv.mm"
include "cico.mm"
include "ccom.mm"
include "cfv.mm"
include "cixp.mm"
include "ciun.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "crrx.mm"
include "cds.mm"
include "cbl.mm"
include "co.mm"
include "crp.mm"
include "cr.mm"
include "cmap.mm"
include "cxmt.mm"
include "cmopn.mm"
include "cme.mm"
include "cfn.mm"
include "eqid.mm"
include "rrxmetfi.mm"
include "syl.mm"
include "metxmet.mm"
include "adantr.mm"
include "ctopn.mm"
include "crefld.mm"
include "cfrlm.mm"
include "ctch.mm"
include "wceq.mm"
include "rrxval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "ovex.mm"
include "tchtopn.mm"
include "ax-mp.mm"
include "a1i.mm"
include "eqcomd.mm"
include "3eqtrd.mm"
include "eleqtrd.mm"
include "simpr.mm"
include "mopni2.mm"
include "syl3anc.mm"
include "w3a.mm"
include "cq.mm"
include "ad2antrr.mm"
include "ctopon.mm"
include "rrxtoponfi.mm"
include "toponss.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "hoiqssbl.mm"
include "3adant3.mm"
include "wi.mm"
include "cop.mm"
include "cmpt.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfixp1.mm"
include "nfel.mm"
include "nfss.mm"
include "nfan.mm"
include "nf3an.mm"
include "3ad2ant1.mm"
include "wf.mm"
include "elmapi.mm"
include "3ad2ant2.mm"
include "adantl.mm"
include "simp3r.mm"
include "simp1r.mm"
include "simp3l.mm"
include "opnvonmbllem1.mm"
include "3exp.mm"
include "adantlr.mm"
include "3adant2.mm"
include "rexlimdvv.mm"
include "mpd.mm"
include "rexlimdv.mm"
include "eliun.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "cxp.mm"
include "crab.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "rabid.mm"
include "sylib.mm"
include "simprd.mm"
include "iunss.mm"
include "eqssd.mm"
include "dmovnsal.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "qct.mm"
include "xpct.mm"
include "mpct.mm"
include "ssct.mm"
include "c1st.mm"
include "c2nd.mm"
include "reex.mm"
include "xpex.mm"
include "qssre.mm"
include "xpss12.mm"
include "mp2an.mm"
include "mapss.mm"
include "sseli.mm"
include "sseldi.mm"
include "fveq2.mm"
include "cbvmptv.mm"
include "hoicoto2.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "fmptd.mm"
include "xp2nd.mm"
include "hoimbl.mm"
include "eqeltrd.mm"
include "saliuncl.mm"

theorem opnvonmbllem2
  let wph: wff ph
  let cS: class S
  let vh: setvar h
  let vi: setvar i
  let cG: class G
  let cK: class K
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vx: setvar x
  let vk: setvar k
  assume opnvonmbllem2.x: |- ( ph -> X e. Fin )
  assume opnvonmbllem2.n: |- S = dom ( voln ` X )
  assume opnvonmbllem2.g: |- ( ph -> G e. ( TopOpen ` ( RR^ ` X ) ) )
  assume opnvonmbl.k: |- K = { h e. ( ( QQ X. QQ ) ^m X ) | X_ i e. X ( ( [,) o. h ) ` i ) C_ G }

  disjoint G h
  disjoint G i
  disjoint h i
  disjoint K h
  disjoint K i
  disjoint S h
  disjoint S i
  disjoint X h
  disjoint X i
  disjoint h ph
  disjoint i ph
  disjoint G c
  disjoint G d
  disjoint G e
  disjoint G x
  disjoint c d
  disjoint c e
  disjoint c h
  disjoint c i
  disjoint c x
  disjoint d e
  disjoint d h
  disjoint d i
  disjoint d x
  disjoint e h
  disjoint e i
  disjoint e x
  disjoint h x
  disjoint i x
  disjoint K c
  disjoint K d
  disjoint K e
  disjoint K x
  disjoint K k
  disjoint h k
  disjoint i k
  disjoint X c
  disjoint X d
  disjoint X e
  disjoint X x
  disjoint X k
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint ph x
  disjoint k ph
  disjoint k x
  assert |- ( ph -> G e. S )

  proof
    wph
    cG
    vh
    cK
    vi
    cX
    vi
    cv
    #
    cico
    vh
    cv
    #
    ccom
    cfv
    cixp
    #
    ciun
    #
    cS
    wph
    cG
    @3
    wph
    vx
    cv
    #
    @3
    wcel
    #
    vx
    cG
    wral
    cG
    @3
    wss
    wph
    @5
    vx
    cG
    wph
    @4
    cG
    wcel
    #
    wa
    #
    @4
    @2
    wcel
    vh
    cK
    wrex
    #
    @5
    @7
    @4
    ve
    cv
    #
    cX
    crrx
    cfv
    #
    cds
    cfv
    #
    cbl
    cfv
    co
    #
    cG
    wss
    #
    ve
    crp
    wrex
    #
    @8
    @7
    @11
    cr
    cX
    cmap
    co
    #
    cxmt
    cfv
    wcel
    #
    cG
    @11
    cmopn
    cfv
    #
    wcel
    #
    @6
    @14
    wph
    @16
    @6
    wph
    @11
    @15
    cme
    cfv
    wcel
    #
    @16
    wph
    cX
    cfn
    wcel
    #
    @19
    opnvonmbllem2.x
    @11
    cX
    @11
    eqid
    rrxmetfi
    syl
    @11
    @15
    metxmet
    syl
    adantr
    wph
    @18
    @6
    wph
    cG
    @10
    ctopn
    cfv
    #
    @17
    opnvonmbllem2.g
    wph
    @21
    crefld
    cX
    cfrlm
    co
    #
    ctch
    cfv
    #
    ctopn
    cfv
    #
    @23
    cds
    cfv
    #
    cmopn
    cfv
    #
    @17
    wph
    @10
    @23
    ctopn
    wph
    @20
    @10
    @23
    wceq
    opnvonmbllem2.x
    @10
    cX
    cfn
    @10
    eqid
    rrxval
    syl
    #
    fveq2d
    @24
    @26
    wceq
    #
    wph
    @22
    cvv
    wcel
    @28
    crefld
    cX
    cfrlm
    ovex
    @25
    @23
    @24
    cvv
    @22
    @23
    eqid
    @25
    eqid
    @24
    eqid
    tchtopn
    ax-mp
    a1i
    wph
    @25
    @11
    cmopn
    wph
    @23
    @10
    cds
    wph
    @10
    @23
    @27
    eqcomd
    fveq2d
    fveq2d
    3eqtrd
    eleqtrd
    adantr
    wph
    @6
    simpr
    #
    ve
    cG
    @11
    @4
    @17
    @15
    @17
    eqid
    mopni2
    syl3anc
    @7
    @13
    @8
    ve
    crp
    @7
    @9
    crp
    wcel
    #
    @13
    @8
    @7
    @30
    @13
    w3a
    #
    @4
    vi
    cX
    @0
    vc
    cv
    #
    cfv
    #
    @0
    vd
    cv
    #
    cfv
    #
    cico
    co
    #
    cixp
    #
    wcel
    #
    @37
    @12
    wss
    #
    wa
    #
    vd
    cq
    cX
    cmap
    co
    #
    wrex
    vc
    @41
    wrex
    #
    @8
    @7
    @30
    @42
    @13
    @7
    @30
    wa
    vi
    @9
    cX
    @4
    vc
    vd
    wph
    @20
    @6
    @30
    opnvonmbllem2.x
    ad2antrr
    @7
    @4
    @15
    wcel
    @30
    @7
    cG
    @15
    @4
    wph
    cG
    @15
    wss
    #
    @6
    wph
    @21
    @15
    ctopon
    cfv
    wcel
    #
    cG
    @21
    wcel
    @43
    wph
    @20
    @44
    opnvonmbllem2.x
    cX
    @21
    @21
    eqid
    rrxtoponfi
    syl
    opnvonmbllem2.g
    cG
    @21
    @15
    toponss
    syl2anc
    adantr
    @29
    sseldd
    adantr
    @7
    @30
    simpr
    hoiqssbl
    3adant3
    @31
    @40
    @8
    vc
    vd
    @41
    @41
    @7
    @13
    @32
    @41
    wcel
    #
    @34
    @41
    wcel
    #
    wa
    #
    @40
    @8
    wi
    wi
    #
    @30
    wph
    @13
    @48
    @6
    wph
    @13
    wa
    #
    @47
    @40
    @8
    @49
    @47
    @40
    w3a
    @12
    @32
    @34
    vh
    vi
    cG
    vi
    cX
    @33
    @35
    cop
    cmpt
    #
    cK
    cfn
    cX
    @4
    @49
    @47
    @40
    vi
    @49
    vi
    nfv
    @47
    vi
    nfv
    @38
    @39
    vi
    vi
    @4
    @37
    vi
    @4
    nfcv
    vi
    cX
    @36
    nfixp1
    #
    nfel
    vi
    @37
    @12
    @51
    vi
    @12
    nfcv
    nfss
    nfan
    nf3an
    @49
    @47
    @20
    @40
    wph
    @20
    @13
    opnvonmbllem2.x
    adantr
    3ad2ant1
    @47
    @49
    cX
    cq
    @32
    wf
    #
    @40
    @45
    @52
    @46
    @32
    cq
    cX
    elmapi
    adantr
    3ad2ant2
    @47
    @49
    cX
    cq
    @34
    wf
    #
    @40
    @46
    @53
    @45
    @34
    cq
    cX
    elmapi
    adantl
    3ad2ant2
    @49
    @47
    @38
    @39
    simp3r
    wph
    @13
    @47
    @40
    simp1r
    @49
    @47
    @38
    @39
    simp3l
    opnvonmbl.k
    @50
    eqid
    opnvonmbllem1
    3exp
    adantlr
    3adant2
    rexlimdvv
    mpd
    3exp
    rexlimdv
    mpd
    vh
    @4
    cK
    @2
    eliun
    sylibr
    ralrimiva
    vx
    cG
    @3
    dfss3
    sylibr
    wph
    @2
    cG
    wss
    #
    vh
    cK
    wral
    @3
    cG
    wss
    wph
    @54
    vh
    cK
    wph
    @1
    cK
    wcel
    #
    wa
    #
    @1
    cq
    cq
    cxp
    #
    cX
    cmap
    co
    #
    wcel
    #
    @54
    @56
    @1
    @54
    vh
    @58
    crab
    #
    wcel
    #
    @59
    @54
    wa
    @55
    @61
    wph
    @55
    @61
    cK
    @60
    @1
    opnvonmbl.k
    eleq2i
    biimpi
    adantl
    @54
    vh
    @58
    rabid
    sylib
    simprd
    ralrimiva
    vh
    cK
    @2
    cG
    iunss
    sylibr
    eqssd
    wph
    cS
    vh
    @2
    cK
    wph
    cS
    cX
    opnvonmbllem2.x
    opnvonmbllem2.n
    dmovnsal
    wph
    cK
    @58
    wss
    #
    @58
    com
    cdom
    wbr
    cK
    com
    cdom
    wbr
    @62
    wph
    cK
    @60
    @58
    opnvonmbl.k
    @54
    vh
    @58
    ssrab2
    eqsstri
    #
    a1i
    wph
    @57
    cX
    wph
    cq
    com
    cdom
    wbr
    #
    @64
    @57
    com
    cdom
    wbr
    @64
    wph
    qct
    a1i
    #
    @65
    cq
    cq
    xpct
    syl2anc
    opnvonmbllem2.x
    mpct
    cK
    @58
    ssct
    syl2anc
    @56
    @2
    vi
    cX
    @0
    vk
    cX
    vk
    cv
    #
    @1
    cfv
    #
    c1st
    cfv
    #
    cmpt
    #
    cfv
    @0
    vk
    cX
    @67
    c2nd
    cfv
    #
    cmpt
    #
    cfv
    cico
    co
    cixp
    cS
    @56
    @69
    @71
    vi
    @1
    cX
    @55
    cX
    cr
    cr
    cxp
    #
    @1
    wf
    #
    wph
    @55
    @1
    @72
    cX
    cmap
    co
    #
    wcel
    @73
    @55
    @58
    @74
    @1
    @72
    cvv
    wcel
    @57
    @72
    wss
    #
    @58
    @74
    wss
    cr
    cr
    reex
    reex
    xpex
    cq
    cr
    wss
    #
    @76
    @75
    qssre
    qssre
    cq
    cr
    cq
    cr
    xpss12
    mp2an
    @57
    @72
    cX
    cvv
    mapss
    mp2an
    cK
    @58
    @1
    @63
    sseli
    sseldi
    @1
    @72
    cX
    elmapi
    syl
    adantl
    #
    vk
    vi
    cX
    @68
    @0
    @1
    cfv
    #
    c1st
    cfv
    @66
    @0
    wceq
    #
    @67
    @78
    c1st
    @66
    @0
    @1
    fveq2
    #
    fveq2d
    cbvmptv
    vk
    vi
    cX
    @70
    @78
    c2nd
    cfv
    @79
    @67
    @78
    c2nd
    @80
    fveq2d
    cbvmptv
    hoicoto2
    @56
    @69
    @71
    cS
    vi
    cX
    wph
    @20
    @55
    opnvonmbllem2.x
    adantr
    opnvonmbllem2.n
    @56
    vk
    cX
    @68
    cr
    @69
    @56
    @66
    cX
    wcel
    wa
    #
    @67
    @72
    wcel
    #
    @68
    cr
    wcel
    @56
    cX
    @72
    @66
    @1
    @77
    ffvelrnda
    #
    @67
    cr
    cr
    xp1st
    syl
    @69
    eqid
    fmptd
    @56
    vk
    cX
    @70
    cr
    @71
    @81
    @82
    @70
    cr
    wcel
    @83
    @67
    cr
    cr
    xp2nd
    syl
    @71
    eqid
    fmptd
    hoimbl
    eqeltrd
    saliuncl
    eqeltrd
end
