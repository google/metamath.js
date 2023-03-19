include "c0.mm"
include "wceq.mm"
include "csumge0.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "fveq2.mm"
include "sge00.mm"
include "a1i.mm"
include "eqtrd.mm"
include "0e0iccpnf.mm"
include "eqeltrd.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "crn.mm"
include "adantr.mm"
include "wf.mm"
include "simpr.mm"
include "sge0pnfval.mm"
include "pnfel0pnf.mm"
include "adantlr.mm"
include "wne.mm"
include "simpll.mm"
include "neqne.mm"
include "ad2antlr.mm"
include "cxr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "csu.mm"
include "cmpt.mm"
include "clt.mm"
include "csup.mm"
include "fge0iccico.mm"
include "sge0reval.mm"
include "wss.mm"
include "cr.mm"
include "wral.mm"
include "elinel2.mm"
include "ad2antrr.mm"
include "elinel1.mm"
include "elpwi.mm"
include "syl.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "adantllr.mm"
include "nne.mm"
include "biimpi.mm"
include "eqcomd.mm"
include "w3a.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "3ad2ant1.mm"
include "3impa.mm"
include "fdm.mm"
include "eleqtrd.mm"
include "fvelrn.mm"
include "syl2anc.mm"
include "ad5ant134.mm"
include "ad3antrrr.mm"
include "condan.mm"
include "ge0xrre.mm"
include "fsumrecl.mm"
include "ralrimiva.mm"
include "eqid.mm"
include "rnmptss.mm"
include "ressxr.mm"
include "sstrd.mm"
include "supxrcl.mm"
include "wex.mm"
include "cle.mm"
include "wbr.mm"
include "neneq.mm"
include "wrel.mm"
include "wb.mm"
include "frel.mm"
include "reldm0.mm"
include "mtbid.mm"
include "neqned.mm"
include "eqnetrd.mm"
include "n0.mm"
include "sylib.mm"
include "wi.mm"
include "ffvelrnda.mm"
include "rexrd.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "wrex.mm"
include "csn.mm"
include "snelpwi.mm"
include "snfi.mm"
include "elind.mm"
include "cc.mm"
include "recnd.mm"
include "sumsn.mm"
include "sumeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "elrnmpt.mm"
include "mpbird.mm"
include "supxrub.mm"
include "breqtrd.mm"
include "xrletrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"
include "pnfge.mm"
include "eliccxrd.mm"
include "syl21anc.mm"
include "pm2.61dan.mm"

theorem sge0cl
  let wph: wff ph
  let cF: class F
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume sge0cl.x: |- ( ph -> X e. V )
  assume sge0cl.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )


  assert |- ( ph -> ( sum^ ` F ) e. ( 0 [,] +oo ) )

  proof
    wph
    cF
    c0
    wceq
    #
    cF
    csumge0
    cfv
    #
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @0
    @3
    wph
    @0
    @1
    cc0
    @2
    @0
    @1
    c0
    csumge0
    cfv
    #
    cc0
    cF
    c0
    csumge0
    fveq2
    @4
    cc0
    wceq
    @0
    sge00
    a1i
    eqtrd
    cc0
    @2
    wcel
    @0
    0e0iccpnf
    a1i
    eqeltrd
    adantl
    wph
    @0
    wn
    #
    wa
    #
    cpnf
    cF
    crn
    #
    wcel
    #
    @3
    wph
    @8
    @3
    @5
    wph
    @8
    wa
    #
    @1
    cpnf
    @2
    @9
    cF
    cV
    cX
    wph
    cX
    cV
    wcel
    #
    @8
    sge0cl.x
    adantr
    wph
    cX
    @2
    cF
    wf
    #
    @8
    sge0cl.f
    adantr
    wph
    @8
    simpr
    sge0pnfval
    cpnf
    @2
    wcel
    @9
    pnfel0pnf
    a1i
    eqeltrd
    adantlr
    @6
    @8
    wn
    #
    wa
    wph
    cF
    c0
    wne
    #
    @12
    @3
    wph
    @5
    @12
    simpll
    @5
    @13
    wph
    @12
    cF
    c0
    neqne
    ad2antlr
    @6
    @12
    simpr
    wph
    @13
    wa
    #
    @12
    wa
    #
    cc0
    cpnf
    @1
    cc0
    cxr
    wcel
    #
    @15
    0xr
    a1i
    cpnf
    cxr
    wcel
    #
    @15
    pnfxr
    a1i
    wph
    @12
    @1
    cxr
    wcel
    #
    @13
    wph
    @12
    wa
    #
    @1
    vx
    cX
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    cfv
    #
    vy
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cxr
    @19
    vx
    vy
    cF
    cV
    cX
    wph
    @10
    @12
    sge0cl.x
    adantr
    @19
    cF
    cX
    wph
    @11
    @12
    sge0cl.f
    adantr
    wph
    @12
    simpr
    #
    fge0iccico
    sge0reval
    #
    @19
    @27
    cxr
    wss
    #
    @28
    cxr
    wcel
    @19
    @27
    cr
    cxr
    @19
    @25
    cr
    wcel
    #
    vx
    @21
    wral
    @27
    cr
    wss
    @19
    @32
    vx
    @21
    @19
    @22
    @21
    wcel
    #
    wa
    #
    @22
    @24
    vy
    @33
    @22
    cfn
    wcel
    @19
    @22
    @20
    cfn
    elinel2
    adantl
    @34
    @23
    @22
    wcel
    #
    wa
    #
    @24
    @2
    wcel
    #
    @24
    cpnf
    wne
    #
    @24
    cr
    wcel
    wph
    @33
    @35
    @37
    @12
    wph
    @33
    wa
    #
    @35
    wa
    #
    cX
    @2
    @23
    cF
    wph
    @11
    @33
    @35
    sge0cl.f
    ad2antrr
    @40
    @22
    cX
    @23
    @39
    @22
    cX
    wss
    #
    @35
    @33
    @41
    wph
    @33
    @22
    @20
    wcel
    @41
    @22
    @20
    cfn
    elinel1
    @22
    cX
    elpwi
    syl
    adantl
    adantr
    @39
    @35
    simpr
    sseldd
    #
    ffvelrnd
    adantllr
    @36
    @38
    @8
    @36
    @38
    wn
    #
    wa
    cpnf
    @24
    @7
    @43
    cpnf
    @24
    wceq
    @36
    @43
    @24
    cpnf
    @43
    @24
    cpnf
    wceq
    @24
    cpnf
    nne
    biimpi
    eqcomd
    adantl
    wph
    @33
    @35
    @24
    @7
    wcel
    #
    @12
    @43
    wph
    @33
    @35
    w3a
    #
    cF
    wfun
    #
    @23
    cF
    cdm
    #
    wcel
    @44
    wph
    @33
    @46
    @35
    wph
    @11
    @46
    sge0cl.f
    cX
    @2
    cF
    ffun
    #
    syl
    3ad2ant1
    @45
    @23
    cX
    @47
    wph
    @33
    @35
    @23
    cX
    wcel
    @42
    3impa
    wph
    @33
    cX
    @47
    wceq
    #
    @35
    wph
    @47
    cX
    wph
    @11
    @47
    cX
    wceq
    sge0cl.f
    cX
    @2
    cF
    fdm
    syl
    eqcomd
    #
    3ad2ant1
    eleqtrd
    @23
    cF
    fvelrn
    syl2anc
    ad5ant134
    eqeltrd
    @19
    @12
    @33
    @35
    @43
    @29
    ad3antrrr
    condan
    @24
    ge0xrre
    syl2anc
    fsumrecl
    ralrimiva
    vx
    @21
    @25
    cr
    @26
    @26
    eqid
    #
    rnmptss
    syl
    cr
    cxr
    wss
    @19
    ressxr
    a1i
    sstrd
    #
    @27
    supxrcl
    syl
    eqeltrd
    #
    adantlr
    @15
    vz
    cv
    #
    cX
    wcel
    #
    vz
    wex
    #
    cc0
    @1
    cle
    wbr
    #
    @14
    @56
    @12
    @14
    cX
    c0
    wne
    @56
    @14
    cX
    @47
    c0
    wph
    @49
    @13
    @50
    adantr
    @14
    @47
    c0
    @14
    @0
    @47
    c0
    wceq
    #
    @13
    @5
    wph
    cF
    c0
    neneq
    adantl
    @14
    cF
    wrel
    #
    @0
    @58
    wb
    wph
    @59
    @13
    wph
    @11
    @59
    sge0cl.f
    cX
    @2
    cF
    frel
    syl
    adantr
    cF
    reldm0
    syl
    mtbid
    neqned
    eqnetrd
    vz
    cX
    n0
    sylib
    adantr
    @15
    @55
    @57
    vz
    wph
    @12
    @55
    @57
    wi
    @13
    @19
    @55
    @57
    @19
    @55
    wa
    #
    cc0
    @54
    cF
    cfv
    #
    @1
    @16
    @60
    0xr
    a1i
    @60
    @61
    @60
    @61
    @2
    wcel
    #
    @61
    cpnf
    wne
    #
    @61
    cr
    wcel
    wph
    @55
    @62
    @12
    wph
    cX
    @2
    @54
    cF
    sge0cl.f
    ffvelrnda
    #
    adantlr
    #
    @60
    @63
    @8
    @60
    @63
    wn
    #
    wa
    cpnf
    @61
    @7
    @66
    cpnf
    @61
    wceq
    @60
    @66
    @61
    cpnf
    @66
    @61
    cpnf
    wceq
    @61
    cpnf
    nne
    biimpi
    eqcomd
    adantl
    @60
    @61
    @7
    wcel
    #
    @66
    wph
    @55
    @67
    @12
    wph
    @55
    wa
    #
    @46
    @54
    @47
    wcel
    @67
    @68
    @11
    @46
    wph
    @11
    @55
    sge0cl.f
    adantr
    @48
    syl
    @68
    @54
    cX
    @47
    wph
    @55
    simpr
    wph
    @49
    @55
    @50
    adantr
    eleqtrd
    @54
    cF
    fvelrn
    syl2anc
    adantlr
    adantr
    eqeltrd
    @19
    @12
    @55
    @66
    @29
    ad2antrr
    condan
    @61
    ge0xrre
    syl2anc
    #
    rexrd
    @19
    @18
    @55
    @53
    adantr
    wph
    @55
    cc0
    @61
    cle
    wbr
    #
    @12
    @68
    @16
    @17
    @62
    @70
    @16
    @68
    0xr
    a1i
    @17
    @68
    pnfxr
    a1i
    @64
    cc0
    cpnf
    @61
    iccgelb
    syl3anc
    adantlr
    @60
    @61
    @28
    @1
    cle
    @60
    @31
    @61
    @27
    wcel
    #
    @61
    @28
    cle
    wbr
    @19
    @31
    @55
    @52
    adantr
    @60
    @71
    @61
    @25
    wceq
    #
    vx
    @21
    wrex
    #
    @60
    @54
    csn
    #
    @21
    wcel
    #
    @61
    @74
    @24
    vy
    csu
    #
    wceq
    #
    @73
    @55
    @75
    @19
    @55
    @20
    cfn
    @74
    @54
    cX
    snelpwi
    @74
    cfn
    wcel
    @55
    @54
    snfi
    a1i
    elind
    adantl
    @60
    @76
    @61
    @60
    @55
    @61
    cc
    wcel
    @76
    @61
    wceq
    @19
    @55
    simpr
    @60
    @61
    @69
    recnd
    @24
    @61
    vy
    @54
    cX
    @23
    @54
    cF
    fveq2
    sumsn
    syl2anc
    eqcomd
    @72
    @77
    vx
    @74
    @21
    @22
    @74
    wceq
    @25
    @76
    @61
    @22
    @74
    @24
    vy
    sumeq1
    eqeq2d
    rspcev
    syl2anc
    @60
    @62
    @71
    @73
    wb
    @65
    vx
    @21
    @25
    @61
    @26
    @2
    @51
    elrnmpt
    syl
    mpbird
    @27
    @61
    supxrub
    syl2anc
    @19
    @28
    @1
    wceq
    @55
    @19
    @1
    @28
    @30
    eqcomd
    adantr
    breqtrd
    xrletrd
    ex
    adantlr
    exlimdv
    mpd
    wph
    @12
    @1
    cpnf
    cle
    wbr
    #
    @13
    @19
    @18
    @78
    @53
    @1
    pnfge
    syl
    adantlr
    eliccxrd
    syl21anc
    pm2.61dan
    pm2.61dan
end
