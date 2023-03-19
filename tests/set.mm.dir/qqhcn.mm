include "cnrg.mm"
include "cdr.mm"
include "cin.mm"
include "wcel.mm"
include "cnlm.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "cq.mm"
include "cqqh.mm"
include "ccn.mm"
include "co.mm"
include "ccnp.mm"
include "wa.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "wf.mm"
include "cv.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "inss2.mm"
include "sseli.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "cdvr.mm"
include "czrh.mm"
include "eqid.mm"
include "qqhf.mm"
include "syl2anc.mm"
include "simpr.mm"
include "cnm.mm"
include "cc.mm"
include "qsscn.mm"
include "sseldi.mm"
include "cneg.mm"
include "0cn.mm"
include "cnmetdval.mm"
include "mpan.mm"
include "df-neg.mm"
include "fveq2i.mm"
include "a1i.mm"
include "absneg.mm"
include "3eqtr2d.mm"
include "syl.mm"
include "cz.mm"
include "zssq.mm"
include "0z.mm"
include "sselii.mm"
include "ovresd.mm"
include "qqhnm.mm"
include "adantlr.mm"
include "3eqtr4d.mm"
include "csg.mm"
include "ad2antrr.mm"
include "ffvelrnd.mm"
include "cngp.mm"
include "inss1.mm"
include "nrgngp.mm"
include "ngpdsr.mm"
include "syl3anc.mm"
include "c0g.mm"
include "qqh0.mm"
include "oveq2d.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "grpsubid1.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "breq1d.mm"
include "biimpd.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "cxmt.mm"
include "wb.mm"
include "cxme.mm"
include "ccnfld.mm"
include "cress.mm"
include "cvv.mm"
include "cnfldxms.mm"
include "qex.mm"
include "ressxms.mm"
include "mp2an.mm"
include "eqeltri.mm"
include "qrngbas.mm"
include "cnfldds.mm"
include "ressds.mm"
include "ax-mp.mm"
include "xmsxmet2.mm"
include "mp1i.mm"
include "ngpxms.mm"
include "3syl.mm"
include "reseq1i.mm"
include "xmstopn.mm"
include "metcnp.mm"
include "mpbir2and.mm"
include "fveq1d.mm"
include "eleqtrrd.mm"
include "ctmd.mm"
include "cghm.mm"
include "ctgp.mm"
include "csubg.mm"
include "cnfldtgp.mm"
include "csubrg.mm"
include "qsubdrg.mm"
include "simpli.mm"
include "subrgsubg.mm"
include "subgtgp.mm"
include "tgptmd.mm"
include "ctrg.mm"
include "nrgtrg.mm"
include "trgtmd2.mm"
include "qqhghm.mm"
include "ghmcnp.mm"
include "mpbid.mm"
include "simprd.mm"

theorem qqhcn
  let cQ: class Q
  let cR: class R
  let cJ: class J
  let cK: class K
  let cZ: class Z
  let vd: setvar d
  let ve: setvar e
  let vq: setvar q
  assume qqhcn.q: |- Q = ( CCfld |`s QQ )
  assume qqhcn.j: |- J = ( TopOpen ` Q )
  assume qqhcn.z: |- Z = ( ZMod ` R )
  assume qqhcn.k: |- K = ( TopOpen ` R )


  assert |- ( ( R e. ( NrmRing i^i DivRing ) /\ Z e. NrmMod /\ ( chr ` R ) = 0 ) -> ( QQHom ` R ) e. ( J Cn K ) )

  proof
    cR
    cnrg
    cdr
    cin
    #
    wcel
    #
    cZ
    cnlm
    wcel
    #
    cR
    cchr
    cfv
    cc0
    wceq
    #
    w3a
    #
    cc0
    cq
    wcel
    #
    cR
    cqqh
    cfv
    #
    cJ
    cK
    ccn
    co
    wcel
    #
    @4
    @6
    cc0
    cJ
    cK
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @5
    @7
    wa
    #
    @4
    @6
    cc0
    cJ
    cR
    cds
    cfv
    #
    cR
    cbs
    cfv
    #
    @13
    cxp
    cres
    #
    cmopn
    cfv
    #
    ccnp
    co
    #
    cfv
    #
    @9
    @4
    @6
    @17
    wcel
    #
    cq
    @13
    @6
    wf
    #
    cc0
    vq
    cv
    #
    cabs
    cmin
    ccom
    #
    cq
    cq
    cxp
    #
    cres
    #
    co
    #
    vd
    cv
    #
    clt
    wbr
    #
    cc0
    @6
    cfv
    #
    @20
    @6
    cfv
    #
    @14
    co
    #
    ve
    cv
    #
    clt
    wbr
    #
    wi
    #
    vq
    cq
    wral
    #
    vd
    crp
    wrex
    #
    ve
    crp
    wral
    #
    @4
    cR
    cdr
    wcel
    #
    @3
    @19
    @1
    @2
    @36
    @3
    @0
    cdr
    cR
    cnrg
    cdr
    inss2
    sseli
    3ad2ant1
    #
    @1
    @2
    @3
    simp3
    #
    @13
    cR
    cdvr
    cfv
    #
    cR
    cR
    czrh
    cfv
    #
    @13
    eqid
    #
    @39
    eqid
    #
    @40
    eqid
    #
    qqhf
    syl2anc
    #
    @4
    @34
    ve
    crp
    @4
    @30
    crp
    wcel
    #
    wa
    #
    @45
    @24
    @30
    clt
    wbr
    #
    @31
    wi
    #
    vq
    cq
    wral
    #
    @34
    @4
    @45
    simpr
    @46
    @48
    vq
    cq
    @46
    @20
    cq
    wcel
    #
    wa
    #
    @47
    @31
    @51
    @24
    @29
    @30
    clt
    @51
    @24
    @28
    cR
    cnm
    cfv
    #
    cfv
    #
    @29
    @51
    cc0
    @20
    @21
    co
    #
    @20
    cabs
    cfv
    #
    @24
    @53
    @51
    @20
    cc
    wcel
    #
    @54
    @55
    wceq
    @51
    cq
    cc
    @20
    qsscn
    @46
    @50
    simpr
    #
    sseldi
    @56
    @54
    cc0
    @20
    cmin
    co
    #
    cabs
    cfv
    #
    @20
    cneg
    #
    cabs
    cfv
    #
    @55
    cc0
    cc
    wcel
    @56
    @54
    @59
    wceq
    0cn
    cc0
    @20
    @21
    @21
    eqid
    cnmetdval
    mpan
    @61
    @59
    wceq
    @56
    @60
    @58
    cabs
    @20
    df-neg
    fveq2i
    a1i
    @20
    absneg
    3eqtr2d
    syl
    @51
    cc0
    @20
    @21
    cq
    @5
    @51
    cz
    cq
    cc0
    zssq
    0z
    sselii
    #
    a1i
    #
    @57
    ovresd
    @4
    @50
    @53
    @55
    wceq
    @45
    @20
    cR
    @52
    cZ
    @52
    eqid
    #
    qqhcn.z
    qqhnm
    adantlr
    3eqtr4d
    @51
    @29
    @27
    @28
    @12
    co
    #
    @28
    @27
    cR
    csg
    cfv
    #
    co
    #
    @52
    cfv
    #
    @53
    @51
    @27
    @28
    @12
    @13
    @51
    cq
    @13
    cc0
    @6
    @4
    @19
    @45
    @50
    @44
    ad2antrr
    #
    @63
    ffvelrnd
    #
    @51
    cq
    @13
    @20
    @6
    @69
    @57
    ffvelrnd
    #
    ovresd
    @51
    cR
    cngp
    wcel
    #
    @27
    @13
    wcel
    @28
    @13
    wcel
    #
    @65
    @68
    wceq
    @51
    cR
    cnrg
    wcel
    #
    @72
    @4
    @74
    @45
    @50
    @1
    @2
    @74
    @3
    @0
    cnrg
    cR
    cnrg
    cdr
    inss1
    sseli
    #
    3ad2ant1
    #
    ad2antrr
    cR
    nrgngp
    #
    syl
    #
    @70
    @71
    @27
    @28
    @12
    cR
    @66
    @52
    @13
    @64
    @41
    @66
    eqid
    #
    @12
    eqid
    #
    ngpdsr
    syl3anc
    @51
    @67
    @28
    @52
    @51
    @67
    @28
    cR
    c0g
    cfv
    #
    @66
    co
    #
    @28
    @51
    @27
    @81
    @28
    @66
    @51
    @36
    @3
    @27
    @81
    wceq
    @4
    @36
    @45
    @50
    @37
    ad2antrr
    @4
    @3
    @45
    @50
    @38
    ad2antrr
    @13
    @39
    cR
    @40
    @41
    @42
    @43
    qqh0
    syl2anc
    oveq2d
    @51
    cR
    cgrp
    wcel
    #
    @73
    @82
    @28
    wceq
    @51
    @72
    @83
    @78
    cR
    ngpgrp
    syl
    @71
    @13
    cR
    @66
    @28
    @81
    @41
    @81
    eqid
    @79
    grpsubid1
    syl2anc
    eqtrd
    fveq2d
    3eqtrd
    eqtr4d
    breq1d
    biimpd
    ralrimiva
    @33
    @49
    vd
    @30
    crp
    @25
    @30
    wceq
    #
    @32
    @48
    vq
    cq
    @84
    @26
    @47
    @31
    @25
    @30
    @24
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ralrimiva
    @4
    @23
    cq
    cxmt
    cfv
    wcel
    #
    @14
    @13
    cxmt
    cfv
    wcel
    #
    @5
    @18
    @19
    @35
    wa
    wb
    cQ
    cxme
    wcel
    #
    @85
    @4
    cQ
    ccnfld
    cq
    cress
    co
    #
    cxme
    qqhcn.q
    ccnfld
    cxme
    wcel
    cq
    cvv
    wcel
    #
    @88
    cxme
    wcel
    cnfldxms
    qex
    cq
    ccnfld
    cvv
    ressxms
    mp2an
    eqeltri
    #
    @21
    cQ
    cq
    cQ
    qqhcn.q
    qrngbas
    #
    @89
    @21
    cQ
    cds
    cfv
    #
    wceq
    qex
    cq
    @21
    ccnfld
    cQ
    cvv
    qqhcn.q
    cnfldds
    ressds
    ax-mp
    #
    xmsxmet2
    mp1i
    @4
    cR
    cxme
    wcel
    #
    @86
    @1
    @2
    @94
    @3
    @1
    @74
    @72
    @94
    @75
    @77
    cR
    ngpxms
    3syl
    3ad2ant1
    #
    @12
    cR
    @13
    @41
    @80
    xmsxmet2
    syl
    @5
    @4
    @62
    a1i
    ve
    vd
    vq
    @23
    @14
    cc0
    @6
    cJ
    @15
    cq
    @13
    @87
    cJ
    @23
    cmopn
    cfv
    wceq
    @90
    @23
    cJ
    cQ
    cq
    qqhcn.j
    @91
    @21
    @92
    @22
    @93
    reseq1i
    xmstopn
    ax-mp
    @15
    eqid
    metcnp
    syl3anc
    mpbir2and
    @4
    cc0
    @8
    @16
    @4
    cK
    @15
    cJ
    ccnp
    @4
    @94
    cK
    @15
    wceq
    @95
    @14
    cK
    cR
    @13
    qqhcn.k
    @41
    @14
    eqid
    xmstopn
    syl
    oveq2d
    fveq1d
    eleqtrrd
    @4
    cQ
    ctmd
    wcel
    #
    cR
    ctmd
    wcel
    #
    @6
    cQ
    cR
    cghm
    co
    wcel
    #
    @10
    @11
    wb
    cQ
    ctgp
    wcel
    #
    @96
    @4
    ccnfld
    ctgp
    wcel
    cq
    ccnfld
    csubg
    cfv
    wcel
    #
    @99
    cnfldtgp
    cq
    ccnfld
    csubrg
    cfv
    wcel
    #
    @100
    @101
    @88
    cdr
    wcel
    qsubdrg
    simpli
    cq
    ccnfld
    subrgsubg
    ax-mp
    cq
    ccnfld
    cQ
    qqhcn.q
    subgtgp
    mp2an
    cQ
    tgptmd
    mp1i
    @4
    @74
    cR
    ctrg
    wcel
    @97
    @76
    cR
    nrgtrg
    cR
    trgtmd2
    3syl
    @4
    @36
    @3
    @98
    @37
    @38
    @13
    @39
    cQ
    cR
    @40
    @41
    @42
    @43
    qqhcn.q
    qqhghm
    syl2anc
    cc0
    @6
    cQ
    cR
    cJ
    cK
    cq
    @91
    qqhcn.j
    qqhcn.k
    ghmcnp
    syl3anc
    mpbid
    simprd
end
