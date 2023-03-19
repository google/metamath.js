include "cnghm.mm"
include "co.mm"
include "wcel.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "ccn.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cghm.mm"
include "nghmghm.mm"
include "eqid.mm"
include "ghmf.mm"
include "syl.mm"
include "wa.mm"
include "cnmo.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "simprr.mm"
include "nghmcl.mm"
include "cngp.mm"
include "cc0.mm"
include "cle.mm"
include "nghmrcl1.mm"
include "nghmrcl2.mm"
include "nmoge0.mm"
include "syl3anc.mm"
include "ge0p1rpd.mm"
include "adantr.mm"
include "rpdivcld.mm"
include "cmul.mm"
include "cmt.mm"
include "cr.mm"
include "ngpms.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "simpr.mm"
include "mscl.mm"
include "rpred.mm"
include "ltmuldiv2d.mm"
include "ffvelrnd.mm"
include "remulcld.mm"
include "nmods.mm"
include "3expa.mm"
include "adantlrr.mm"
include "cxme.mm"
include "msxms.mm"
include "xmsge0.mm"
include "lep1d.mm"
include "lemul1ad.mm"
include "letrd.mm"
include "lelttr.mm"
include "mpand.mm"
include "sylbird.mm"
include "ovresd.mm"
include "breq1d.mm"
include "3imtr4d.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimivva.mm"
include "cxmt.mm"
include "wb.mm"
include "xmsxmet.mm"
include "3syl.mm"
include "metcn.mm"
include "mpbir2and.mm"
include "mstopn.mm"
include "oveq12d.mm"
include "eleqtrrd.mm"

theorem nghmcn
  let cS: class S
  let cT: class T
  let cF: class F
  let cJ: class J
  let cK: class K
  let vr: setvar r
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume nghmcn.j: |- J = ( TopOpen ` S )
  assume nghmcn.k: |- K = ( TopOpen ` T )


  assert |- ( F e. ( S NGHom T ) -> F e. ( J Cn K ) )

  proof
    cF
    cS
    cT
    cnghm
    co
    wcel
    #
    cF
    cS
    cds
    cfv
    #
    cS
    cbs
    cfv
    #
    @2
    cxp
    cres
    #
    cmopn
    cfv
    #
    cT
    cds
    cfv
    #
    cT
    cbs
    cfv
    #
    @6
    cxp
    cres
    #
    cmopn
    cfv
    #
    ccn
    co
    #
    cJ
    cK
    ccn
    co
    @0
    cF
    @9
    wcel
    #
    @2
    @6
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    @3
    co
    #
    vs
    cv
    #
    clt
    wbr
    #
    @12
    cF
    cfv
    #
    @13
    cF
    cfv
    #
    @7
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    wi
    #
    vy
    @2
    wral
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    vx
    @2
    wral
    #
    @0
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    @11
    cS
    cT
    cF
    nghmghm
    #
    cS
    cT
    cF
    @2
    @6
    @2
    eqid
    #
    @6
    eqid
    #
    ghmf
    syl
    #
    @0
    @24
    vx
    vr
    @2
    crp
    @0
    @12
    @2
    wcel
    #
    @20
    crp
    wcel
    #
    wa
    #
    wa
    #
    @20
    cF
    cS
    cT
    cnmo
    co
    #
    cfv
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    crp
    wcel
    @14
    @38
    clt
    wbr
    #
    @21
    wi
    #
    vy
    @2
    wral
    #
    @24
    @34
    @20
    @37
    @0
    @31
    @32
    simprr
    #
    @0
    @37
    crp
    wcel
    #
    @33
    @0
    @36
    cS
    cT
    cF
    @35
    @35
    eqid
    #
    nghmcl
    #
    @0
    cS
    cngp
    wcel
    #
    cT
    cngp
    wcel
    #
    @26
    cc0
    @36
    cle
    wbr
    cS
    cT
    cF
    nghmrcl1
    #
    cS
    cT
    cF
    nghmrcl2
    #
    @27
    cS
    cT
    cF
    @35
    @44
    nmoge0
    syl3anc
    ge0p1rpd
    #
    adantr
    rpdivcld
    @34
    @40
    vy
    @2
    @34
    @13
    @2
    wcel
    #
    wa
    #
    @12
    @13
    @1
    co
    #
    @38
    clt
    wbr
    #
    @17
    @18
    @5
    co
    #
    @20
    clt
    wbr
    #
    @39
    @21
    @52
    @54
    @37
    @53
    cmul
    co
    #
    @20
    clt
    wbr
    #
    @56
    @52
    @53
    @20
    @37
    @52
    cS
    cmt
    wcel
    #
    @31
    @51
    @53
    cr
    wcel
    @0
    @59
    @33
    @51
    @0
    @46
    @59
    @48
    cS
    ngpms
    syl
    #
    ad2antrr
    #
    @0
    @31
    @32
    @51
    simplrl
    #
    @34
    @51
    simpr
    #
    @12
    @13
    @1
    cS
    @2
    @28
    @1
    eqid
    #
    mscl
    syl3anc
    #
    @52
    @20
    @34
    @32
    @51
    @42
    adantr
    rpred
    #
    @0
    @43
    @33
    @51
    @50
    ad2antrr
    #
    ltmuldiv2d
    @52
    @55
    @57
    cle
    wbr
    #
    @58
    @56
    @52
    @55
    @36
    @53
    cmul
    co
    #
    @57
    @52
    cT
    cmt
    wcel
    #
    @17
    @6
    wcel
    @18
    @6
    wcel
    @55
    cr
    wcel
    #
    @0
    @70
    @33
    @51
    @0
    @47
    @70
    @49
    cT
    ngpms
    syl
    #
    ad2antrr
    @52
    @2
    @6
    @12
    cF
    @0
    @11
    @33
    @51
    @30
    ad2antrr
    #
    @62
    ffvelrnd
    #
    @52
    @2
    @6
    @13
    cF
    @73
    @63
    ffvelrnd
    #
    @17
    @18
    @5
    cT
    @6
    @29
    @5
    eqid
    #
    mscl
    syl3anc
    #
    @52
    @36
    @53
    @0
    @36
    cr
    wcel
    @33
    @51
    @45
    ad2antrr
    #
    @65
    remulcld
    @52
    @37
    @53
    @52
    @37
    @67
    rpred
    #
    @65
    remulcld
    #
    @0
    @31
    @51
    @55
    @69
    cle
    wbr
    #
    @32
    @0
    @31
    @51
    @81
    @12
    @13
    @1
    @5
    cS
    cT
    cF
    @35
    @2
    @44
    @28
    @64
    @76
    nmods
    3expa
    adantlrr
    @52
    @36
    @37
    @53
    @78
    @79
    @65
    @52
    cS
    cxme
    wcel
    #
    @31
    @51
    cc0
    @53
    cle
    wbr
    @52
    @59
    @82
    @61
    cS
    msxms
    #
    syl
    @62
    @63
    @12
    @13
    @1
    cS
    @2
    @28
    @64
    xmsge0
    syl3anc
    @52
    @36
    @78
    lep1d
    lemul1ad
    letrd
    @52
    @71
    @57
    cr
    wcel
    @20
    cr
    wcel
    @68
    @58
    wa
    @56
    wi
    @77
    @80
    @66
    @55
    @57
    @20
    lelttr
    syl3anc
    mpand
    sylbird
    @52
    @14
    @53
    @38
    clt
    @52
    @12
    @13
    @1
    @2
    @62
    @63
    ovresd
    breq1d
    @52
    @19
    @55
    @20
    clt
    @52
    @17
    @18
    @5
    @6
    @74
    @75
    ovresd
    breq1d
    3imtr4d
    ralrimiva
    @23
    @41
    vs
    @38
    crp
    @15
    @38
    wceq
    #
    @22
    @40
    vy
    @2
    @84
    @16
    @39
    @21
    @15
    @38
    @14
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ralrimivva
    @0
    @3
    @2
    cxmt
    cfv
    wcel
    #
    @7
    @6
    cxmt
    cfv
    wcel
    #
    @10
    @11
    @25
    wa
    wb
    @0
    @59
    @82
    @85
    @60
    @83
    @3
    cS
    @2
    @28
    @3
    eqid
    #
    xmsxmet
    3syl
    @0
    @70
    cT
    cxme
    wcel
    @86
    @72
    cT
    msxms
    @7
    cT
    @6
    @29
    @7
    eqid
    #
    xmsxmet
    3syl
    vx
    vr
    vs
    vy
    @3
    @7
    cF
    @4
    @8
    @2
    @6
    @4
    eqid
    @8
    eqid
    metcn
    syl2anc
    mpbir2and
    @0
    cJ
    @4
    cK
    @8
    ccn
    @0
    @59
    cJ
    @4
    wceq
    @60
    @3
    cJ
    cS
    @2
    nghmcn.j
    @28
    @87
    mstopn
    syl
    @0
    @70
    cK
    @8
    wceq
    @72
    @7
    cK
    cT
    @6
    nghmcn.k
    @29
    @88
    mstopn
    syl
    oveq12d
    eleqtrrd
end
