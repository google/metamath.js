include "caddc.mm"
include "cof.mm"
include "co.mm"
include "cr.mm"
include "cvv.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "readdcl.mm"
include "adantl.mm"
include "citg1.mm"
include "cdm.mm"
include "wf.mm"
include "i1ff.mm"
include "syl.mm"
include "reex.mm"
include "a1i.mm"
include "inidm.mm"
include "off.mm"
include "crn.mm"
include "cmpt2.mm"
include "cfn.mm"
include "wss.mm"
include "cxp.mm"
include "wfo.mm"
include "i1frn.mm"
include "xpfi.mm"
include "syl2anc.mm"
include "wfn.mm"
include "eqid.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "dffn4.mm"
include "mpbi.mm"
include "fofi.mm"
include "sylancl.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "rspceov.mm"
include "mp3an3.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "elab.mm"
include "sylibr.mm"
include "ffn.mm"
include "dffn3.mm"
include "sylib.mm"
include "frn.mm"
include "rnmpt2.mm"
include "syl6sseqr.mm"
include "ssfi.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "ccnv.mm"
include "cima.mm"
include "cmin.mm"
include "cin.mm"
include "ciun.mm"
include "cvol.mm"
include "cc.mm"
include "ssdifssd.mm"
include "sselda.mm"
include "recnd.mm"
include "i1faddlem.mm"
include "syldan.mm"
include "wral.mm"
include "adantr.mm"
include "cmbf.mm"
include "ad2antrr.mm"
include "i1fmbf.mm"
include "eldifi.mm"
include "ad2antlr.mm"
include "sseldd.mm"
include "resubcld.mm"
include "mbfimasn.mm"
include "syl3anc.mm"
include "inmbl.mm"
include "ralrimiva.mm"
include "finiunmbl.mm"
include "eqeltrd.mm"
include "cfv.mm"
include "covol.mm"
include "mblvol.mm"
include "csu.mm"
include "cle.mm"
include "wbr.mm"
include "mblss.mm"
include "inss1.mm"
include "adantrr.mm"
include "simprr.mm"
include "oveq2d.mm"
include "subid1d.mm"
include "eqtrd.mm"
include "sneqd.mm"
include "imaeq2d.mm"
include "fveq2d.mm"
include "i1fima2sn.mm"
include "sylan.mm"
include "eqeltrrd.mm"
include "ovolsscl.mm"
include "expr.mm"
include "wne.mm"
include "eldifsn.mm"
include "inss2.mm"
include "sylan2.mm"
include "i1fima.mm"
include "sylan2br.mm"
include "pm2.61dne.mm"
include "fsumrecl.mm"
include "syl5ss.mm"
include "jca.mm"
include "ovolfiniun.mm"
include "eqbrtrd.mm"
include "ovollecl.mm"
include "i1fd.mm"

theorem i1fadd
  let wph: wff ph
  let cF: class F
  let cG: class G
  let vi: setvar i
  let vj: setvar j
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w
  let cI: class I
  let vv: setvar v
  let vx: setvar x
  let cP: class P
  let vu: setvar u
  assume i1fadd.1: |- ( ph -> F e. dom S.1 )
  assume i1fadd.2: |- ( ph -> G e. dom S.1 )


  assert |- ( ph -> ( F oF + G ) e. dom S.1 )

  proof
    wph
    vy
    cF
    cG
    caddc
    cof
    co
    #
    wph
    vx
    vy
    cr
    cr
    cr
    caddc
    cr
    cr
    cr
    cF
    cG
    cvv
    cvv
    vx
    cv
    #
    cr
    wcel
    vy
    cv
    #
    cr
    wcel
    wa
    @1
    @2
    caddc
    co
    #
    cr
    wcel
    wph
    @1
    @2
    readdcl
    adantl
    wph
    cF
    citg1
    cdm
    #
    wcel
    #
    cr
    cr
    cF
    wf
    #
    i1fadd.1
    cF
    i1ff
    syl
    #
    wph
    cG
    @4
    wcel
    #
    cr
    cr
    cG
    wf
    #
    i1fadd.2
    cG
    i1ff
    syl
    #
    cr
    cvv
    wcel
    wph
    reex
    a1i
    #
    @11
    cr
    inidm
    #
    off
    #
    wph
    vu
    vv
    cF
    crn
    #
    cG
    crn
    #
    vu
    cv
    #
    vv
    cv
    #
    caddc
    co
    #
    cmpt2
    #
    crn
    #
    cfn
    wcel
    #
    @0
    crn
    #
    @20
    wss
    @22
    cfn
    wcel
    wph
    @14
    @15
    cxp
    #
    cfn
    wcel
    #
    @23
    @20
    @19
    wfo
    #
    @21
    wph
    @14
    cfn
    wcel
    #
    @15
    cfn
    wcel
    #
    @24
    wph
    @5
    @26
    i1fadd.1
    cF
    i1frn
    syl
    wph
    @8
    @27
    i1fadd.2
    cG
    i1frn
    syl
    #
    @14
    @15
    xpfi
    syl2anc
    @19
    @23
    wfn
    @25
    vu
    vv
    @14
    @15
    @18
    @19
    @19
    eqid
    #
    @16
    @17
    caddc
    ovex
    fnmpt2i
    @23
    @19
    dffn4
    mpbi
    @23
    @20
    @19
    fofi
    sylancl
    wph
    @22
    vw
    cv
    #
    @18
    wceq
    #
    vv
    @15
    wrex
    vu
    @14
    wrex
    #
    vw
    cab
    #
    @20
    wph
    cr
    @33
    @0
    wf
    @22
    @33
    wss
    wph
    vx
    vy
    cr
    cr
    cr
    caddc
    @14
    @15
    @33
    cF
    cG
    cvv
    cvv
    @1
    @14
    wcel
    #
    @2
    @15
    wcel
    #
    wa
    #
    @3
    @33
    wcel
    #
    wph
    @36
    @3
    @18
    wceq
    #
    vv
    @15
    wrex
    vu
    @14
    wrex
    #
    @37
    @34
    @35
    @3
    @3
    wceq
    @39
    @3
    eqid
    vu
    vv
    @14
    @15
    @1
    @2
    @3
    caddc
    rspceov
    mp3an3
    @32
    @39
    vw
    @3
    @1
    @2
    caddc
    ovex
    @30
    @3
    wceq
    @31
    @38
    vu
    vv
    @14
    @15
    @30
    @3
    @18
    eqeq1
    2rexbidv
    elab
    sylibr
    adantl
    wph
    cF
    cr
    wfn
    #
    cr
    @14
    cF
    wf
    wph
    @6
    @40
    @7
    cr
    cr
    cF
    ffn
    syl
    cr
    cF
    dffn3
    sylib
    wph
    cG
    cr
    wfn
    #
    cr
    @15
    cG
    wf
    wph
    @9
    @41
    @10
    cr
    cr
    cG
    ffn
    syl
    cr
    cG
    dffn3
    sylib
    @11
    @11
    @12
    off
    cr
    @33
    @0
    frn
    syl
    vu
    vv
    vw
    @14
    @15
    @18
    @19
    @29
    rnmpt2
    syl6sseqr
    @20
    @22
    ssfi
    syl2anc
    wph
    @2
    @22
    cc0
    csn
    #
    cdif
    #
    wcel
    #
    wa
    #
    @0
    ccnv
    @2
    csn
    #
    cima
    #
    vz
    @15
    cF
    ccnv
    #
    @2
    vz
    cv
    #
    cmin
    co
    #
    csn
    #
    cima
    #
    cG
    ccnv
    @49
    csn
    #
    cima
    #
    cin
    #
    ciun
    #
    cvol
    cdm
    #
    wph
    @44
    @2
    cc
    wcel
    #
    @47
    @56
    wceq
    @45
    @2
    wph
    @43
    cr
    @2
    wph
    @22
    cr
    @42
    wph
    cr
    cr
    @0
    wf
    #
    @22
    cr
    wss
    #
    @13
    cr
    cr
    @0
    frn
    #
    syl
    ssdifssd
    sselda
    recnd
    #
    wph
    vz
    @2
    cF
    cG
    i1fadd.1
    i1fadd.2
    i1faddlem
    syldan
    #
    @45
    @27
    @55
    @57
    wcel
    #
    vz
    @15
    wral
    @56
    @57
    wcel
    wph
    @27
    @44
    @28
    adantr
    #
    @45
    @64
    vz
    @15
    @45
    @49
    @15
    wcel
    #
    wa
    #
    @52
    @57
    wcel
    #
    @54
    @57
    wcel
    #
    @64
    @67
    cF
    cmbf
    wcel
    #
    @6
    @50
    cr
    wcel
    @68
    @67
    @5
    @70
    wph
    @5
    @44
    @66
    i1fadd.1
    ad2antrr
    cF
    i1fmbf
    syl
    wph
    @6
    @44
    @66
    @7
    ad2antrr
    @67
    @2
    @49
    @67
    @22
    cr
    @2
    @67
    @59
    @60
    wph
    @59
    @44
    @66
    @13
    ad2antrr
    @61
    syl
    @44
    @2
    @22
    wcel
    wph
    @66
    @2
    @22
    @42
    eldifi
    ad2antlr
    sseldd
    @45
    @15
    cr
    @49
    @45
    @9
    @15
    cr
    wss
    wph
    @9
    @44
    @10
    adantr
    cr
    cr
    cG
    frn
    syl
    sselda
    #
    resubcld
    cr
    @50
    cF
    mbfimasn
    syl3anc
    #
    @67
    cG
    cmbf
    wcel
    #
    @9
    @49
    cr
    wcel
    @69
    @67
    @8
    @73
    wph
    @8
    @44
    @66
    i1fadd.2
    ad2antrr
    cG
    i1fmbf
    syl
    wph
    @9
    @44
    @66
    @10
    ad2antrr
    @71
    cr
    @49
    cG
    mbfimasn
    syl3anc
    #
    @52
    @54
    inmbl
    syl2anc
    ralrimiva
    @15
    @55
    vz
    finiunmbl
    syl2anc
    eqeltrd
    #
    @45
    @47
    cvol
    cfv
    #
    @47
    covol
    cfv
    #
    cr
    @45
    @47
    @57
    wcel
    #
    @76
    @77
    wceq
    @75
    @47
    mblvol
    syl
    @45
    @47
    cr
    wss
    #
    @15
    @55
    covol
    cfv
    #
    vz
    csu
    #
    cr
    wcel
    @77
    @81
    cle
    wbr
    @77
    cr
    wcel
    @45
    @78
    @79
    @75
    @47
    mblss
    syl
    @45
    @15
    @80
    vz
    @65
    @67
    @80
    cr
    wcel
    #
    @49
    cc0
    @45
    @66
    @49
    cc0
    wceq
    #
    @82
    @45
    @66
    @83
    wa
    #
    wa
    #
    @55
    @52
    wss
    #
    @52
    cr
    wss
    #
    @52
    covol
    cfv
    #
    cr
    wcel
    @82
    @86
    @85
    @52
    @54
    inss1
    a1i
    @85
    @68
    @87
    @45
    @66
    @68
    @83
    @72
    adantrr
    #
    @52
    mblss
    syl
    @85
    @52
    cvol
    cfv
    #
    @88
    cr
    @85
    @68
    @90
    @88
    wceq
    @89
    @52
    mblvol
    syl
    @85
    @90
    @48
    @46
    cima
    #
    cvol
    cfv
    #
    cr
    @85
    @52
    @91
    cvol
    @85
    @51
    @46
    @48
    @85
    @50
    @2
    @85
    @50
    @2
    cc0
    cmin
    co
    @2
    @85
    @49
    cc0
    @2
    cmin
    @45
    @66
    @83
    simprr
    oveq2d
    @85
    @2
    @45
    @58
    @84
    @62
    adantr
    subid1d
    eqtrd
    sneqd
    imaeq2d
    fveq2d
    @45
    @92
    cr
    wcel
    #
    @84
    wph
    @5
    @44
    @93
    i1fadd.1
    @2
    @22
    cF
    i1fima2sn
    sylan
    adantr
    eqeltrd
    eqeltrrd
    @55
    @52
    ovolsscl
    syl3anc
    expr
    @45
    @66
    @49
    cc0
    wne
    #
    @82
    @66
    @94
    wa
    @45
    @49
    @15
    @42
    cdif
    wcel
    #
    @82
    @49
    @15
    cc0
    eldifsn
    @45
    @95
    wa
    #
    @55
    @54
    wss
    #
    @54
    cr
    wss
    #
    @54
    covol
    cfv
    #
    cr
    wcel
    @82
    @97
    @96
    @52
    @54
    inss2
    #
    a1i
    @95
    @45
    @66
    @98
    @49
    @15
    @42
    eldifi
    @67
    @69
    @98
    @74
    @54
    mblss
    syl
    #
    sylan2
    @96
    @54
    cvol
    cfv
    #
    @99
    cr
    @96
    @69
    @102
    @99
    wceq
    wph
    @69
    @44
    @95
    wph
    @8
    @69
    i1fadd.2
    @53
    cG
    i1fima
    syl
    ad2antrr
    @54
    mblvol
    syl
    @45
    @8
    @95
    @102
    cr
    wcel
    wph
    @8
    @44
    i1fadd.2
    adantr
    @49
    @15
    cG
    i1fima2sn
    sylan
    eqeltrrd
    @55
    @54
    ovolsscl
    syl3anc
    sylan2br
    expr
    pm2.61dne
    #
    fsumrecl
    @45
    @77
    @56
    covol
    cfv
    #
    @81
    cle
    @45
    @47
    @56
    covol
    @63
    fveq2d
    @45
    @27
    @55
    cr
    wss
    #
    @82
    wa
    #
    vz
    @15
    wral
    @104
    @81
    cle
    wbr
    @65
    @45
    @106
    vz
    @15
    @67
    @105
    @82
    @67
    @55
    @54
    cr
    @100
    @101
    syl5ss
    @103
    jca
    ralrimiva
    @15
    @55
    vz
    ovolfiniun
    syl2anc
    eqbrtrd
    @47
    @81
    ovollecl
    syl3anc
    eqeltrd
    i1fd
end
