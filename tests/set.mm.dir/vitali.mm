include "cr.mm"
include "wwe.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cvol.mm"
include "cdm.mm"
include "wpss.mm"
include "cvv.mm"
include "cuni.mm"
include "wex.mm"
include "reex.mm"
include "pwex.mm"
include "cxp.mm"
include "cin.mm"
include "weinxp.mm"
include "wceq.mm"
include "wb.mm"
include "unipw.mm"
include "weeq2.mm"
include "ax-mp.mm"
include "bitr4i.mm"
include "xpex.mm"
include "inex2.mm"
include "weeq1.mm"
include "spcev.mm"
include "sylbi.mm"
include "dfac8c.mm"
include "mpsyl.mm"
include "wa.mm"
include "cn.mm"
include "cq.mm"
include "c1.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "cdom.mm"
include "qex.mm"
include "inex1.mm"
include "cdiv.mm"
include "nnrecq.mm"
include "cle.mm"
include "nnrecre.mm"
include "cc0.mm"
include "neg1rr.mm"
include "a1i.mm"
include "0re.mm"
include "neg1lt0.mm"
include "ltleii.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "rpge0d.mm"
include "letrd.mm"
include "nnge1.mm"
include "clt.mm"
include "nnre.mm"
include "nngt0.mm"
include "1re.mm"
include "0lt1.mm"
include "lerec.mm"
include "mpanl12.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "1div1e1.mm"
include "syl6breq.mm"
include "elicc2i.mm"
include "syl3anbrc.mm"
include "elind.mm"
include "weq.mm"
include "oveq2.mm"
include "nncn.mm"
include "nnne0.mm"
include "recrecd.mm"
include "eqeqan12d.mm"
include "syl5ib.mm"
include "impbid1.mm"
include "dom2.mm"
include "wss.mm"
include "inss1.mm"
include "ssdomg.mm"
include "mp2.mm"
include "qnnen.mm"
include "domentr.mm"
include "mp2an.mm"
include "sbth.mm"
include "bren.mm"
include "mpbi.mm"
include "cmin.mm"
include "copab.mm"
include "cqs.mm"
include "cmpt.mm"
include "crn.mm"
include "cdif.mm"
include "wn.mm"
include "crab.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "oveq12.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "cbvopabv.mm"
include "eqid.mm"
include "wfn.mm"
include "fvex.mm"
include "fnmpti.mm"
include "neeq1.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "wtru.mm"
include "wer.mm"
include "vitalilem1.mm"
include "qsss.mm"
include "trud.mm"
include "unitssre.mm"
include "sspwb.mm"
include "sstri.mm"
include "ssralv.mm"
include "fvmpt.mm"
include "imbi2d.mm"
include "ralbiia.mm"
include "sylibr.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "oveq1.mm"
include "cbvrabv.mm"
include "oveq2d.mm"
include "rabbidv.mm"
include "syl5eq.mm"
include "cbvmptv.mm"
include "simprr.mm"
include "vitalilem5.mm"
include "pm2.21i.mm"
include "expr.mm"
include "pm2.18d.mm"
include "eldif.mm"
include "mblss.mm"
include "selpw.mm"
include "ssriv.mm"
include "ssnelpss.mm"
include "syl.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpi.mm"
include "exlimddv.mm"

theorem vitali
  let c.lt: class .<
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( .< We RR -> dom vol C. ~P RR )

  proof
    cr
    c.lt
    wwe
    #
    vz
    cv
    #
    c0
    wne
    #
    @1
    vf
    cv
    #
    cfv
    #
    @1
    wcel
    #
    wi
    #
    vz
    cr
    cpw
    #
    wral
    #
    cvol
    cdm
    #
    @7
    wpss
    #
    vf
    @7
    cvv
    wcel
    @0
    @7
    cuni
    #
    vx
    cv
    #
    wwe
    #
    vx
    wex
    #
    @8
    vf
    wex
    cr
    reex
    pwex
    @0
    @11
    c.lt
    cr
    cr
    cxp
    #
    cin
    #
    wwe
    #
    @14
    @0
    cr
    @16
    wwe
    #
    @17
    cr
    c.lt
    weinxp
    @11
    cr
    wceq
    @17
    @18
    wb
    cr
    unipw
    @11
    cr
    @16
    weeq2
    ax-mp
    bitr4i
    @13
    @17
    vx
    @16
    @15
    c.lt
    cr
    cr
    reex
    reex
    xpex
    inex2
    @11
    @12
    @16
    weeq1
    spcev
    sylbi
    vz
    @7
    cvv
    vf
    vx
    dfac8c
    mpsyl
    @0
    @8
    wa
    #
    cn
    cq
    c1
    cneg
    #
    c1
    cicc
    co
    #
    cin
    #
    vg
    cv
    #
    wf1o
    #
    vg
    wex
    #
    @10
    cn
    @22
    cen
    wbr
    #
    @25
    cn
    @22
    cdom
    wbr
    #
    @22
    cn
    cdom
    wbr
    #
    @26
    @22
    cvv
    wcel
    @27
    cq
    @21
    qex
    inex1
    vx
    vy
    cn
    @22
    c1
    @12
    cdiv
    co
    #
    c1
    vy
    cv
    #
    cdiv
    co
    #
    cvv
    @12
    cn
    wcel
    #
    cq
    @21
    @29
    @12
    nnrecq
    @32
    @29
    cr
    wcel
    @20
    @29
    cle
    wbr
    @29
    c1
    cle
    wbr
    @29
    @21
    wcel
    @12
    nnrecre
    #
    @32
    @20
    cc0
    @29
    @20
    cr
    wcel
    @32
    neg1rr
    a1i
    cc0
    cr
    wcel
    @32
    0re
    a1i
    @33
    @20
    cc0
    cle
    wbr
    @32
    @20
    cc0
    neg1rr
    0re
    neg1lt0
    ltleii
    a1i
    @32
    @29
    @32
    @12
    @12
    nnrp
    rpreccld
    rpge0d
    letrd
    @32
    @29
    c1
    c1
    cdiv
    co
    #
    c1
    cle
    @32
    c1
    @12
    cle
    wbr
    #
    @29
    @34
    cle
    wbr
    #
    @12
    nnge1
    @32
    @12
    cr
    wcel
    #
    cc0
    @12
    clt
    wbr
    #
    @35
    @36
    wb
    #
    @12
    nnre
    @12
    nngt0
    c1
    cr
    wcel
    cc0
    c1
    clt
    wbr
    @37
    @38
    wa
    @39
    1re
    0lt1
    c1
    @12
    lerec
    mpanl12
    syl2anc
    mpbid
    1div1e1
    syl6breq
    @20
    c1
    @29
    neg1rr
    1re
    elicc2i
    syl3anbrc
    elind
    @32
    @30
    cn
    wcel
    #
    wa
    #
    @29
    @31
    wceq
    #
    vx
    vy
    weq
    #
    @42
    c1
    @29
    cdiv
    co
    #
    c1
    @31
    cdiv
    co
    #
    wceq
    @41
    @43
    @29
    @31
    c1
    cdiv
    oveq2
    @32
    @40
    @44
    @12
    @45
    @30
    @32
    @12
    @12
    nncn
    @12
    nnne0
    recrecd
    @40
    @30
    @30
    nncn
    @30
    nnne0
    recrecd
    eqeqan12d
    syl5ib
    @12
    @30
    c1
    cdiv
    oveq2
    impbid1
    dom2
    ax-mp
    @22
    cq
    cdom
    wbr
    #
    cq
    cn
    cen
    wbr
    @28
    cq
    cvv
    wcel
    @22
    cq
    wss
    @46
    qex
    cq
    @21
    inss1
    @22
    cq
    cvv
    ssdomg
    mp2
    qnnen
    @22
    cq
    cn
    domentr
    mp2an
    cn
    @22
    sbth
    mp2an
    cn
    @22
    vg
    bren
    mpbi
    @19
    @24
    @10
    vg
    @19
    @24
    @10
    @19
    @24
    wa
    #
    vc
    cc0
    c1
    cicc
    co
    #
    va
    cv
    #
    @48
    wcel
    #
    vb
    cv
    #
    @48
    wcel
    #
    wa
    #
    @49
    @51
    cmin
    co
    #
    cq
    wcel
    #
    wa
    #
    va
    vb
    copab
    #
    cqs
    #
    vc
    cv
    #
    @3
    cfv
    #
    cmpt
    #
    crn
    #
    @7
    @9
    cdif
    wcel
    #
    @10
    @47
    @63
    @19
    @24
    @63
    wn
    #
    @63
    @19
    @24
    @64
    wa
    #
    wa
    #
    @63
    @66
    vx
    vy
    vw
    @57
    @58
    vm
    cn
    vt
    cv
    #
    vm
    cv
    #
    @23
    cfv
    #
    cmin
    co
    #
    @62
    wcel
    #
    vt
    cr
    crab
    #
    cmpt
    vn
    @61
    @23
    vs
    @56
    @12
    @48
    wcel
    #
    @30
    @48
    wcel
    #
    wa
    #
    @12
    @30
    cmin
    co
    #
    cq
    wcel
    #
    wa
    va
    vb
    vx
    vy
    va
    vx
    weq
    #
    vb
    vy
    weq
    #
    wa
    #
    @53
    @75
    @55
    @77
    @78
    @50
    @73
    @79
    @52
    @74
    @49
    @12
    @48
    eleq1
    @51
    @30
    @48
    eleq1
    bi2anan9
    @80
    @54
    @76
    cq
    @49
    @12
    @51
    @30
    cmin
    oveq12
    eleq1d
    anbi12d
    cbvopabv
    #
    @58
    eqid
    @61
    @58
    wfn
    @66
    vc
    @58
    @60
    @61
    @59
    @3
    fvex
    @61
    eqid
    #
    fnmpti
    a1i
    @8
    vw
    cv
    #
    c0
    wne
    #
    @83
    @61
    cfv
    #
    @83
    wcel
    #
    wi
    #
    vw
    @58
    wral
    #
    @0
    @65
    @8
    @84
    @83
    @3
    cfv
    #
    @83
    wcel
    #
    wi
    #
    vw
    @58
    wral
    #
    @88
    @8
    @91
    vw
    @7
    wral
    #
    @92
    @6
    @91
    vz
    vw
    @7
    vz
    vw
    weq
    #
    @2
    @84
    @5
    @90
    @1
    @83
    c0
    neeq1
    @94
    @4
    @89
    @1
    @83
    @1
    @83
    @3
    fveq2
    @94
    id
    eleq12d
    imbi12d
    cbvralv
    @58
    @7
    wss
    @93
    @92
    wi
    @58
    @48
    cpw
    #
    @7
    @58
    @95
    wss
    wtru
    @48
    @57
    @48
    @57
    wer
    wtru
    vx
    vy
    @57
    @81
    vitalilem1
    a1i
    qsss
    trud
    @48
    cr
    wss
    @95
    @7
    wss
    unitssre
    @48
    cr
    sspwb
    mpbi
    sstri
    @91
    vw
    @58
    @7
    ssralv
    ax-mp
    sylbi
    @87
    @91
    vw
    @58
    @83
    @58
    wcel
    #
    @86
    @90
    @84
    @96
    @85
    @89
    @83
    vc
    @83
    @60
    @89
    @58
    @61
    @59
    @83
    @3
    fveq2
    @82
    @83
    @3
    fvex
    fvmpt
    eleq1d
    imbi2d
    ralbiia
    sylibr
    ad2antlr
    @19
    @24
    @64
    simprl
    vm
    vn
    cn
    @72
    vs
    cv
    #
    vn
    cv
    #
    @23
    cfv
    #
    cmin
    co
    #
    @62
    wcel
    #
    vs
    cr
    crab
    #
    vm
    vn
    weq
    #
    @72
    @97
    @69
    cmin
    co
    #
    @62
    wcel
    #
    vs
    cr
    crab
    @102
    @71
    @105
    vt
    vs
    cr
    vt
    vs
    weq
    @70
    @104
    @62
    @67
    @97
    @69
    cmin
    oveq1
    eleq1d
    cbvrabv
    @103
    @105
    @101
    vs
    cr
    @103
    @104
    @100
    @62
    @103
    @69
    @99
    @97
    cmin
    @68
    @98
    @23
    fveq2
    oveq2d
    eleq1d
    rabbidv
    syl5eq
    cbvmptv
    @19
    @24
    @64
    simprr
    vitalilem5
    pm2.21i
    expr
    pm2.18d
    @63
    @62
    @7
    wcel
    @62
    @9
    wcel
    wn
    wa
    #
    @10
    @62
    @7
    @9
    eldif
    @9
    @7
    wss
    @106
    @10
    wi
    vx
    @9
    @7
    @12
    @9
    wcel
    @12
    cr
    wss
    @12
    @7
    wcel
    @12
    mblss
    vx
    cr
    selpw
    sylibr
    ssriv
    @9
    @7
    @62
    ssnelpss
    ax-mp
    sylbi
    syl
    ex
    exlimdv
    mpi
    exlimddv
end
