include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cle.mm"
include "cordt.mm"
include "cr.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "ctop.mm"
include "letop.mm"
include "cxr.mm"
include "cxp.mm"
include "wf.mm"
include "wfn.mm"
include "wral.mm"
include "cpw.mm"
include "ioof.mm"
include "ffn.mm"
include "ax-mp.mm"
include "iooordt.mm"
include "rgen2w.mm"
include "ffnov.mm"
include "mpbir2an.mm"
include "frn.mm"
include "tgss.mm"
include "mp2an.mm"
include "wceq.mm"
include "tgtop.mm"
include "sseqtri.mm"
include "sseli.mm"
include "ctopon.mm"
include "retopon.mm"
include "toponss.mm"
include "mpan.mm"
include "wa.mm"
include "wb.mm"
include "reordt.mm"
include "restopn2.mm"
include "sylanbrc.mm"
include "ssriv.mm"
include "cpnf.mm"
include "cioc.mm"
include "cmpt.mm"
include "cmnf.mm"
include "cico.mm"
include "cun.mm"
include "eqid.mm"
include "leordtval.mm"
include "oveq1i.mm"
include "ctb.mm"
include "cvv.mm"
include "eqeltrri.mm"
include "tgclb.mm"
include "mpbir.mm"
include "reex.mm"
include "tgrest.mm"
include "eqtr4i.mm"
include "retopbas.mm"
include "cin.mm"
include "wrex.mm"
include "elrest.mm"
include "wo.mm"
include "elun.mm"
include "vex.mm"
include "elrnmpt.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "simpl.mm"
include "pnfxr.mm"
include "a1i.mm"
include "rexr.mm"
include "adantl.mm"
include "df-ioc.mm"
include "elixx3g.mm"
include "baib.mm"
include "syl3anc.mm"
include "pnfge.mm"
include "syl.mm"
include "biantrud.mm"
include "ltpnf.mm"
include "3bitr2d.mm"
include "pm5.32da.mm"
include "elin.mm"
include "ancom.mm"
include "bitri.mm"
include "3anass.mm"
include "3bitr4g.mm"
include "elioo2.mm"
include "mpan2.mm"
include "bitr4d.mm"
include "eqrdv.mm"
include "ioorebas.mm"
include "syl6eqel.mm"
include "ineq1.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "mnfxr.mm"
include "df-ico.mm"
include "mnfle.mm"
include "biantrurd.mm"
include "mnflt.mm"
include "jaoi.mm"
include "cuni.mm"
include "elssuni.mm"
include "unirnioo.mm"
include "syl6sseqr.mm"
include "df-ss.mm"
include "sylib.mm"
include "id.mm"
include "eqeltrd.mm"
include "eleq1.mm"
include "eqsstri.mm"
include "eqssi.mm"

theorem xrtgioo
  let cJ: class J
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume xrtgioo.1: |- J = ( ( ordTop ` <_ ) |`t RR )


  assert |- ( topGen ` ran (,) ) = J

  proof
    cioo
    crn
    #
    ctg
    cfv
    #
    cle
    cordt
    cfv
    #
    cr
    crest
    co
    #
    cJ
    @1
    @3
    vx
    @1
    @3
    vx
    cv
    #
    @1
    wcel
    #
    @4
    @2
    wcel
    #
    @4
    cr
    wss
    #
    @4
    @3
    wcel
    #
    @1
    @2
    @4
    @1
    @2
    ctg
    cfv
    #
    @2
    @2
    ctop
    wcel
    #
    @0
    @2
    wss
    #
    @1
    @9
    wss
    letop
    cxr
    cxr
    cxp
    #
    @2
    cioo
    wf
    #
    @11
    @13
    cioo
    @12
    wfn
    #
    @4
    vy
    cv
    #
    cioo
    co
    @2
    wcel
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    @12
    cr
    cpw
    #
    cioo
    wf
    @14
    ioof
    @12
    @17
    cioo
    ffn
    ax-mp
    @16
    vx
    vy
    cxr
    cxr
    @4
    @15
    iooordt
    rgen2w
    vx
    vy
    cxr
    cxr
    @2
    cioo
    ffnov
    mpbir2an
    @12
    @2
    cioo
    frn
    ax-mp
    @0
    @2
    ctop
    tgss
    mp2an
    @10
    @9
    @2
    wceq
    letop
    @2
    tgtop
    ax-mp
    sseqtri
    sseli
    @1
    cr
    ctopon
    cfv
    wcel
    @5
    @7
    retopon
    @4
    @1
    cr
    toponss
    mpan
    @10
    cr
    @2
    wcel
    @8
    @6
    @7
    wa
    wb
    letop
    reordt
    cr
    @4
    @2
    restopn2
    mp2an
    sylanbrc
    ssriv
    @3
    vx
    cxr
    @4
    cpnf
    cioc
    co
    #
    cmpt
    #
    crn
    #
    vx
    cxr
    cmnf
    @4
    cico
    co
    #
    cmpt
    #
    crn
    #
    cun
    #
    @0
    cun
    #
    cr
    crest
    co
    #
    ctg
    cfv
    #
    @1
    @3
    @25
    ctg
    cfv
    #
    cr
    crest
    co
    #
    @27
    @2
    @28
    cr
    crest
    vx
    @20
    @23
    @0
    @20
    eqid
    @23
    eqid
    @0
    eqid
    leordtval
    #
    oveq1i
    @25
    ctb
    wcel
    #
    cr
    cvv
    wcel
    #
    @27
    @29
    wceq
    @31
    @28
    ctop
    wcel
    @2
    @28
    ctop
    @30
    letop
    eqeltrri
    @25
    tgclb
    mpbir
    #
    reex
    cr
    @25
    ctb
    cvv
    tgrest
    mp2an
    eqtr4i
    @0
    ctb
    wcel
    @26
    @0
    wss
    @27
    @1
    wss
    retopbas
    vu
    @26
    @0
    vu
    cv
    #
    @26
    wcel
    #
    @34
    vv
    cv
    #
    cr
    cin
    #
    wceq
    #
    vv
    @25
    wrex
    #
    @34
    @0
    wcel
    #
    @31
    @32
    @35
    @39
    wb
    @33
    reex
    vv
    @34
    cr
    @25
    ctb
    cvv
    elrest
    mp2an
    @38
    @40
    vv
    @25
    @36
    @25
    wcel
    #
    @40
    @38
    @37
    @0
    wcel
    #
    @41
    @36
    @24
    wcel
    #
    @36
    @0
    wcel
    #
    wo
    @42
    @36
    @24
    @0
    elun
    @43
    @42
    @44
    @43
    @36
    @20
    wcel
    #
    @36
    @23
    wcel
    #
    wo
    @42
    @36
    @20
    @23
    elun
    @45
    @42
    @46
    @45
    @36
    @18
    wceq
    #
    vx
    cxr
    wrex
    #
    @42
    @36
    cvv
    wcel
    #
    @45
    @48
    wb
    vv
    vex
    #
    vx
    cxr
    @18
    @36
    @19
    cvv
    @19
    eqid
    elrnmpt
    ax-mp
    @47
    @42
    vx
    cxr
    @4
    cxr
    wcel
    #
    @42
    @47
    @18
    cr
    cin
    #
    @0
    wcel
    @51
    @52
    @4
    cpnf
    cioo
    co
    #
    @0
    @51
    vy
    @52
    @53
    @51
    @15
    @52
    wcel
    #
    @15
    cr
    wcel
    #
    @4
    @15
    clt
    wbr
    #
    @15
    cpnf
    clt
    wbr
    #
    w3a
    #
    @15
    @53
    wcel
    #
    @51
    @55
    @15
    @18
    wcel
    #
    wa
    #
    @55
    @56
    @57
    wa
    #
    wa
    @54
    @58
    @51
    @55
    @60
    @62
    @51
    @55
    wa
    #
    @60
    @56
    @15
    cpnf
    cle
    wbr
    #
    wa
    #
    @56
    @62
    @63
    @51
    cpnf
    cxr
    wcel
    #
    @15
    cxr
    wcel
    #
    @60
    @65
    wb
    @51
    @55
    simpl
    #
    @66
    @63
    pnfxr
    a1i
    @55
    @67
    @51
    @15
    rexr
    adantl
    #
    @60
    @51
    @66
    @67
    w3a
    @65
    va
    vb
    vc
    @4
    cpnf
    @15
    clt
    cle
    cioc
    va
    vb
    vc
    df-ioc
    elixx3g
    baib
    syl3anc
    @63
    @64
    @56
    @63
    @67
    @64
    @69
    @15
    pnfge
    syl
    biantrud
    @63
    @57
    @56
    @55
    @57
    @51
    @15
    ltpnf
    adantl
    biantrud
    3bitr2d
    pm5.32da
    @54
    @60
    @55
    wa
    @61
    @15
    @18
    cr
    elin
    @60
    @55
    ancom
    bitri
    @55
    @56
    @57
    3anass
    3bitr4g
    @51
    @66
    @59
    @58
    wb
    pnfxr
    @4
    cpnf
    @15
    elioo2
    mpan2
    bitr4d
    eqrdv
    @4
    cpnf
    ioorebas
    syl6eqel
    @47
    @37
    @52
    @0
    @36
    @18
    cr
    ineq1
    eleq1d
    syl5ibrcom
    rexlimiv
    sylbi
    @46
    @36
    @21
    wceq
    #
    vx
    cxr
    wrex
    #
    @42
    @49
    @46
    @71
    wb
    @50
    vx
    cxr
    @21
    @36
    @22
    cvv
    @22
    eqid
    elrnmpt
    ax-mp
    @70
    @42
    vx
    cxr
    @51
    @42
    @70
    @21
    cr
    cin
    #
    @0
    wcel
    @51
    @72
    cmnf
    @4
    cioo
    co
    #
    @0
    @51
    vy
    @72
    @73
    @51
    @15
    @72
    wcel
    #
    @55
    cmnf
    @15
    clt
    wbr
    #
    @15
    @4
    clt
    wbr
    #
    w3a
    #
    @15
    @73
    wcel
    #
    @51
    @55
    @15
    @21
    wcel
    #
    wa
    #
    @55
    @75
    @76
    wa
    #
    wa
    @74
    @77
    @51
    @55
    @79
    @81
    @63
    @79
    cmnf
    @15
    cle
    wbr
    #
    @76
    wa
    #
    @76
    @81
    @63
    cmnf
    cxr
    wcel
    #
    @51
    @67
    @79
    @83
    wb
    @84
    @63
    mnfxr
    a1i
    @68
    @69
    @79
    @84
    @51
    @67
    w3a
    @83
    va
    vb
    vc
    cmnf
    @4
    @15
    cle
    clt
    cico
    va
    vb
    vc
    df-ico
    elixx3g
    baib
    syl3anc
    @63
    @82
    @76
    @63
    @67
    @82
    @69
    @15
    mnfle
    syl
    biantrurd
    @63
    @75
    @76
    @55
    @75
    @51
    @15
    mnflt
    adantl
    biantrurd
    3bitr2d
    pm5.32da
    @74
    @79
    @55
    wa
    @80
    @15
    @21
    cr
    elin
    @79
    @55
    ancom
    bitri
    @55
    @75
    @76
    3anass
    3bitr4g
    @84
    @51
    @78
    @77
    wb
    mnfxr
    cmnf
    @4
    @15
    elioo2
    mpan
    bitr4d
    eqrdv
    cmnf
    @4
    ioorebas
    syl6eqel
    @70
    @37
    @72
    @0
    @36
    @21
    cr
    ineq1
    eleq1d
    syl5ibrcom
    rexlimiv
    sylbi
    jaoi
    sylbi
    @44
    @37
    @36
    @0
    @44
    @36
    cr
    wss
    @37
    @36
    wceq
    @44
    @36
    @0
    cuni
    cr
    @36
    @0
    elssuni
    unirnioo
    syl6sseqr
    @36
    cr
    df-ss
    sylib
    @44
    id
    eqeltrd
    jaoi
    sylbi
    @34
    @37
    @0
    eleq1
    syl5ibrcom
    rexlimiv
    sylbi
    ssriv
    @26
    @0
    ctb
    tgss
    mp2an
    eqsstri
    eqssi
    xrtgioo.1
    eqtr4i
end
