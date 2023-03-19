include "cres.mm"
include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cuni.mm"
include "cesum.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "w3a.mm"
include "cdm.mm"
include "coms.mm"
include "omsf.mm"
include "syl2anc.mm"
include "a1i.mm"
include "fdm.mm"
include "syl.mm"
include "eqcomd.mm"
include "unieqd.mm"
include "pweqd.mm"
include "feq12d.mm"
include "mpbird.mm"
include "ccarsg.mm"
include "cvv.mm"
include "uniexg.mm"
include "carsgcl.mm"
include "syl5eqss.mm"
include "fssresd.mm"
include "oms0.mm"
include "0elcarsg.mm"
include "syl6eleqr.mm"
include "fvres.mm"
include "eqtrd.mm"
include "nfcv.mm"
include "id.mm"
include "cbvdisj.mm"
include "anbi2i.mm"
include "cle.mm"
include "ciun.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "elpwid.mm"
include "wss.mm"
include "sstrd.mm"
include "sselda.mm"
include "simprl.mm"
include "omssubadd.mm"
include "uniiun.mm"
include "fveq2i.mm"
include "3ad2ant1.mm"
include "simpl3.mm"
include "simpr.mm"
include "sseldd.mm"
include "simp2.mm"
include "syl5eqbr.mm"
include "3adant1r.mm"
include "elpwi.mm"
include "3ad2ant3.mm"
include "omsmon.mm"
include "ad2antlr.mm"
include "syl6sseq.mm"
include "carsgclctun.mm"
include "syl6eq.mm"
include "nfv.mm"
include "ralrimiva.mm"
include "esumeq2d.mm"
include "3brtr4d.mm"
include "csn.mm"
include "cdif.mm"
include "snex.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "elsni.mm"
include "fveq2d.mm"
include "sylan9eqr.mm"
include "esumpad2.mm"
include "neldifsnd.mm"
include "difss.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "domtr.mm"
include "ssdifssd.mm"
include "simprr.mm"
include "sylib.mm"
include "disjss1.mm"
include "mpsyl.mm"
include "carsggect.mm"
include "eqbrtrrd.mm"
include "unidif0.mm"
include "syl6breq.mm"
include "jca.mm"
include "cxr.mm"
include "wb.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "esumcl.mm"
include "xrletri3.mm"
include "sylan2b.mm"
include "ex.mm"
include "3jca.mm"
include "csiga.mm"
include "crn.mm"
include "carsgsiga.mm"
include "syl5eqel.mm"
include "elrnsiga.mm"
include "ismeas.mm"
include "3syl.mm"

theorem omsmeas
  let wph: wff ph
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cM: class M
  let cV: class V
  let ve: setvar e
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vg: setvar g
  assume omsmeas.m: |- M = ( toOMeas ` R )
  assume omsmeas.s: |- S = ( toCaraSiga ` M )
  assume omsmeas.o: |- ( ph -> Q e. V )
  assume omsmeas.r: |- ( ph -> R : Q --> ( 0 [,] +oo ) )
  assume omsmeas.d: |- ( ph -> (/) e. dom R )
  assume omsmeas.0: |- ( ph -> ( R ` (/) ) = 0 )


  assert |- ( ph -> ( M |` S ) e. ( measures ` S ) )

  proof
    wph
    cM
    cS
    cres
    #
    cS
    cmeas
    cfv
    wcel
    #
    cS
    cc0
    cpnf
    cicc
    co
    #
    @0
    wf
    #
    c0
    @0
    cfv
    #
    cc0
    wceq
    #
    ve
    cv
    #
    com
    cdom
    wbr
    #
    vf
    @6
    vf
    cv
    #
    wdisj
    #
    wa
    #
    @6
    cuni
    #
    @0
    cfv
    #
    @6
    @8
    @0
    cfv
    #
    vf
    cesum
    #
    wceq
    #
    wi
    #
    ve
    cS
    cpw
    #
    wral
    #
    w3a
    #
    wph
    @3
    @5
    @18
    wph
    cQ
    cuni
    #
    cpw
    #
    @2
    cS
    cM
    wph
    @21
    @2
    cM
    wf
    #
    cR
    cdm
    #
    cuni
    #
    cpw
    #
    @2
    cR
    coms
    cfv
    #
    wf
    #
    wph
    cQ
    cV
    wcel
    #
    cQ
    @2
    cR
    wf
    #
    @27
    omsmeas.o
    omsmeas.r
    cQ
    cR
    cV
    omsf
    syl2anc
    wph
    @21
    @25
    @2
    cM
    @26
    cM
    @26
    wceq
    wph
    omsmeas.m
    a1i
    wph
    @20
    @24
    wph
    cQ
    @23
    wph
    @23
    cQ
    wph
    @29
    @23
    cQ
    wceq
    omsmeas.r
    cQ
    @2
    cR
    fdm
    syl
    eqcomd
    unieqd
    pweqd
    feq12d
    mpbird
    #
    wph
    cS
    cM
    ccarsg
    cfv
    #
    @21
    omsmeas.s
    wph
    cM
    @20
    cvv
    wph
    @28
    @20
    cvv
    wcel
    #
    omsmeas.o
    cQ
    cV
    uniexg
    syl
    #
    @30
    carsgcl
    syl5eqss
    #
    fssresd
    #
    wph
    @4
    c0
    cM
    cfv
    #
    cc0
    wph
    c0
    cS
    wcel
    @4
    @36
    wceq
    wph
    c0
    @31
    cS
    wph
    cM
    @20
    cvv
    @33
    @30
    wph
    cQ
    cR
    cM
    cV
    omsmeas.m
    omsmeas.o
    omsmeas.r
    omsmeas.d
    omsmeas.0
    oms0
    #
    0elcarsg
    omsmeas.s
    syl6eleqr
    c0
    cS
    cM
    fvres
    syl
    @37
    eqtrd
    wph
    @16
    ve
    @17
    wph
    @6
    @17
    wcel
    #
    wa
    #
    @10
    @15
    @10
    @39
    @7
    vg
    @6
    vg
    cv
    #
    wdisj
    #
    wa
    #
    @15
    @9
    @41
    @7
    vf
    vg
    @6
    @8
    @40
    vg
    @8
    nfcv
    vf
    @40
    nfcv
    @8
    @40
    wceq
    id
    cbvdisj
    anbi2i
    @39
    @42
    wa
    #
    @15
    @12
    @14
    cle
    wbr
    #
    @14
    @12
    cle
    wbr
    #
    wa
    #
    @43
    @44
    @45
    @43
    vf
    @6
    @8
    ciun
    #
    cM
    cfv
    #
    @6
    @8
    cM
    cfv
    #
    vf
    cesum
    #
    @12
    @14
    cle
    @43
    vf
    @8
    cQ
    cR
    cM
    cV
    @6
    omsmeas.m
    wph
    @28
    @38
    @42
    omsmeas.o
    ad2antrr
    wph
    @29
    @38
    @42
    omsmeas.r
    ad2antrr
    @43
    @8
    @6
    wcel
    #
    wa
    #
    @8
    @20
    @43
    @6
    @21
    @8
    @43
    @6
    cS
    @21
    @43
    @6
    cS
    wph
    @38
    @42
    simplr
    #
    elpwid
    wph
    cS
    @21
    wss
    @38
    @42
    @34
    ad2antrr
    sstrd
    sselda
    #
    elpwid
    @39
    @7
    @41
    simprl
    #
    omssubadd
    @43
    @11
    cS
    wcel
    #
    @12
    @48
    wceq
    @43
    @11
    @31
    cS
    @43
    vx
    vy
    @6
    cM
    @20
    cvv
    wph
    @32
    @38
    @42
    @33
    ad2antrr
    #
    wph
    @22
    @38
    @42
    @30
    ad2antrr
    #
    wph
    @36
    cc0
    wceq
    @38
    @42
    @37
    ad2antrr
    #
    @39
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @60
    @21
    wss
    #
    @60
    cuni
    #
    cM
    cfv
    #
    @60
    vy
    cv
    #
    cM
    cfv
    #
    vy
    cesum
    #
    cle
    wbr
    #
    @42
    wph
    @61
    @62
    @68
    @38
    wph
    @61
    @62
    w3a
    #
    @64
    vy
    @60
    @65
    ciun
    #
    cM
    cfv
    @67
    cle
    @63
    @70
    cM
    vy
    @60
    uniiun
    fveq2i
    @69
    vy
    @65
    cQ
    cR
    cM
    cV
    @60
    omsmeas.m
    wph
    @61
    @28
    @62
    omsmeas.o
    3ad2ant1
    wph
    @61
    @29
    @62
    omsmeas.r
    3ad2ant1
    @69
    @65
    @60
    wcel
    #
    wa
    #
    @65
    @20
    @72
    @60
    @21
    @65
    wph
    @61
    @62
    @71
    simpl3
    @69
    @71
    simpr
    sseldd
    elpwid
    wph
    @61
    @62
    simp2
    omssubadd
    syl5eqbr
    #
    3adant1r
    3adant1r
    #
    @39
    @60
    @65
    wss
    #
    @65
    @21
    wcel
    #
    @60
    cM
    cfv
    @66
    cle
    wbr
    #
    @42
    wph
    @75
    @76
    @77
    @38
    wph
    @75
    @76
    w3a
    @60
    @65
    cQ
    cR
    cM
    cV
    omsmeas.m
    wph
    @75
    @28
    @76
    omsmeas.o
    3ad2ant1
    wph
    @75
    @29
    @76
    omsmeas.r
    3ad2ant1
    wph
    @75
    @76
    simp2
    @76
    wph
    @65
    @20
    wss
    @75
    @65
    @20
    elpwi
    3ad2ant3
    omsmon
    #
    3adant1r
    3adant1r
    #
    @55
    @43
    @6
    cS
    @31
    @38
    @6
    cS
    wss
    wph
    @42
    @6
    cS
    elpwi
    ad2antlr
    #
    omsmeas.s
    syl6sseq
    #
    carsgclctun
    omsmeas.s
    syl6eleqr
    #
    @56
    @12
    @11
    cM
    cfv
    #
    @48
    @11
    cS
    cM
    fvres
    #
    @11
    @47
    cM
    vf
    @6
    uniiun
    fveq2i
    syl6eq
    syl
    @43
    @6
    @13
    @49
    vf
    @43
    vf
    nfv
    @43
    @13
    @49
    wceq
    #
    vf
    @6
    @52
    @8
    cS
    wcel
    @85
    @43
    @6
    cS
    @8
    @80
    sselda
    #
    @8
    cS
    cM
    fvres
    syl
    ralrimiva
    esumeq2d
    #
    3brtr4d
    @43
    @50
    @83
    @14
    @12
    cle
    @43
    @50
    @6
    c0
    csn
    #
    cdif
    #
    cuni
    #
    cM
    cfv
    #
    @83
    cle
    @43
    @89
    @49
    vf
    cesum
    @50
    @91
    cle
    @43
    @6
    @88
    @49
    vf
    @17
    cvv
    @53
    @88
    cvv
    wcel
    @43
    c0
    snex
    a1i
    @52
    @21
    @2
    @8
    cM
    @43
    @22
    @51
    @58
    adantr
    @54
    ffvelrnd
    @8
    @88
    wcel
    #
    @43
    @49
    @36
    cc0
    @92
    @8
    c0
    cM
    @8
    c0
    elsni
    fveq2d
    @59
    sylan9eqr
    esumpad2
    @43
    vx
    vy
    vf
    @89
    cM
    @20
    cvv
    @57
    @58
    @59
    @74
    @43
    c0
    @6
    neldifsnd
    @43
    @89
    @6
    cdom
    wbr
    #
    @7
    @89
    com
    cdom
    wbr
    @43
    @38
    @89
    @6
    wss
    #
    @93
    @53
    @6
    @88
    difss
    #
    @89
    @6
    @17
    ssdomg
    mpisyl
    @55
    @89
    @6
    com
    domtr
    syl2anc
    @43
    @6
    @31
    @88
    @81
    ssdifssd
    @94
    @43
    vy
    @6
    @65
    wdisj
    #
    vy
    @89
    @65
    wdisj
    @95
    @43
    @41
    @96
    @39
    @7
    @41
    simprr
    vg
    vy
    @6
    @40
    @65
    vy
    @40
    nfcv
    vg
    @65
    nfcv
    @40
    @65
    wceq
    id
    cbvdisj
    sylib
    vy
    @89
    @6
    @65
    disjss1
    mpsyl
    @79
    carsggect
    eqbrtrrd
    @90
    @11
    cM
    @6
    unidif0
    fveq2i
    syl6breq
    @87
    @43
    @56
    @12
    @83
    wceq
    @82
    @84
    syl
    3brtr4d
    jca
    @43
    @12
    cxr
    wcel
    @14
    cxr
    wcel
    @15
    @46
    wb
    @43
    @2
    cxr
    @12
    cc0
    cpnf
    iccssxr
    #
    @43
    cS
    @2
    @11
    @0
    wph
    @3
    @38
    @42
    @35
    ad2antrr
    #
    @82
    ffvelrnd
    sseldi
    @43
    @2
    cxr
    @14
    @97
    @43
    @38
    @13
    @2
    wcel
    #
    vf
    @6
    wral
    @14
    @2
    wcel
    @53
    @43
    @99
    vf
    @6
    @52
    cS
    @2
    @8
    @0
    @43
    @3
    @51
    @98
    adantr
    @86
    ffvelrnd
    ralrimiva
    @6
    @13
    vf
    @17
    vf
    @6
    nfcv
    esumcl
    syl2anc
    sseldi
    @12
    @14
    xrletri3
    syl2anc
    mpbird
    sylan2b
    ex
    ralrimiva
    3jca
    wph
    cS
    @20
    csiga
    cfv
    #
    wcel
    cS
    csiga
    crn
    cuni
    wcel
    @1
    @19
    wb
    wph
    cS
    @31
    @100
    omsmeas.s
    wph
    vx
    vy
    cM
    @20
    cvv
    @33
    @30
    @37
    @73
    @78
    carsgsiga
    syl5eqel
    cS
    @20
    elrnsiga
    ve
    vf
    cS
    @0
    ismeas
    3syl
    mpbird
end
