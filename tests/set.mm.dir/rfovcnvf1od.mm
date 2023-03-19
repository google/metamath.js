include "cxp.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wa.mm"
include "copab.mm"
include "cmpt.mm"
include "wceq.mm"
include "wbr.mm"
include "crab.mm"
include "eqid.mm"
include "wf.mm"
include "wss.mm"
include "ssrab2.mm"
include "a1i.mm"
include "sselpwd.mm"
include "adantr.mm"
include "fmptd.mm"
include "cvv.mm"
include "pwexg.mm"
include "syl.mm"
include "elmapd.mm"
include "mpbird.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "wtru.mm"
include "wi.mm"
include "biimpa.mm"
include "ffvelrnda.mm"
include "ex.mm"
include "elpwi.mm"
include "sseld.mm"
include "syl6.mm"
include "imdistand.mm"
include "a1tru.mm"
include "jcad.mm"
include "ssopab2dv.mm"
include "opabssxp.mm"
include "syl6ss.mm"
include "wfn.mm"
include "simplrr.mm"
include "elmapfn.mm"
include "wral.mm"
include "ad2antrr.mm"
include "rabexg.mm"
include "ralrimivw.mm"
include "nfcv.mm"
include "fnmptf.mm"
include "3syl.mm"
include "cin.mm"
include "dfin5.mm"
include "simpllr.mm"
include "simprd.mm"
include "elmapi.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "sseqin2.mm"
include "sylib.mm"
include "ibar.mm"
include "rabbidv.mm"
include "adantl.mm"
include "3eqtr3a.mm"
include "cop.mm"
include "weq.mm"
include "breq2.mm"
include "cbvrabv.mm"
include "breq1.mm"
include "df-br.mm"
include "syl6bb.mm"
include "syl5eq.mm"
include "cbvmptv.mm"
include "opeq1d.mm"
include "eleq12d.mm"
include "vex.mm"
include "simpl.mm"
include "eleq1d.mm"
include "fveq2d.mm"
include "anbi12d.mm"
include "opelopaba.mm"
include "ad3antrrr.mm"
include "fvmptd.mm"
include "eqtr4d.mm"
include "eqfnfvd.mm"
include "wrel.mm"
include "simplrl.mm"
include "xpss.mm"
include "df-rel.mm"
include "sylibr.mm"
include "relopab.mm"
include "anim12i.mm"
include "anim1i.mm"
include "wb.mm"
include "elrab.mm"
include "anbi2i.mm"
include "simplr.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "pm5.32da.mm"
include "cdm.mm"
include "opeldm.mm"
include "dmss.mm"
include "dmxpss.mm"
include "syl5.mm"
include "pm4.71rd.mm"
include "crn.mm"
include "opelrn.mm"
include "rnss.mm"
include "rnxpss.mm"
include "anbi2d.mm"
include "bitrd.mm"
include "3bitr4d.mm"
include "syl5rbb.mm"
include "eqrelrdv2.mm"
include "syl21anc.mm"
include "impbida.mm"
include "f1ocnv2d.mm"
include "rfovd.mm"
include "f1oeq1.mm"
include "cnveq.mm"
include "eqeq1d.mm"

theorem rfovcnvf1od
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cF: class F
  let cO: class O
  let cV: class V
  let cW: class W
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  assume rfovd.rf: |- O = ( a e. _V , b e. _V |-> ( r e. ~P ( a X. b ) |-> ( x e. a |-> { y e. b | x r y } ) ) )
  assume rfovd.a: |- ( ph -> A e. V )
  assume rfovd.b: |- ( ph -> B e. W )
  assume rfovcnvf1od.f: |- F = ( A O B )

  disjoint A a
  disjoint A b
  disjoint A f
  disjoint A r
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a f
  disjoint a r
  disjoint a x
  disjoint a y
  disjoint b f
  disjoint b r
  disjoint b x
  disjoint b y
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint r x
  disjoint r y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint B r
  disjoint B x
  disjoint B y
  disjoint W a
  disjoint W x
  disjoint a ph
  disjoint b ph
  disjoint f ph
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint A u
  disjoint a u
  disjoint b u
  disjoint f u
  disjoint r u
  disjoint u x
  disjoint u y
  disjoint A v
  disjoint b v
  disjoint f v
  disjoint r v
  disjoint u v
  disjoint v x
  disjoint v y
  disjoint B u
  disjoint B v
  disjoint W u
  disjoint W v
  disjoint ph u
  assert |- ( ph -> ( F : ~P ( A X. B ) -1-1-onto-> ( ~P B ^m A ) /\ `' F = ( f e. ( ~P B ^m A ) |-> { <. x , y >. | ( x e. A /\ y e. ( f ` x ) ) } ) ) )

  proof
    wph
    cA
    cB
    cxp
    #
    cpw
    #
    cB
    cpw
    #
    cA
    cmap
    co
    #
    cF
    wf1o
    #
    cF
    ccnv
    #
    vf
    @3
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    @6
    vf
    cv
    #
    cfv
    #
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    cmpt
    #
    wceq
    #
    wa
    #
    @1
    @3
    vr
    @1
    vx
    cA
    @6
    @8
    vr
    cv
    #
    wbr
    #
    vy
    cB
    crab
    #
    cmpt
    #
    cmpt
    #
    wf1o
    #
    @21
    ccnv
    #
    @14
    wceq
    #
    wa
    #
    wph
    vr
    vf
    @1
    @3
    @20
    @13
    @21
    @21
    eqid
    wph
    @20
    @3
    wcel
    #
    @17
    @1
    wcel
    #
    wph
    @26
    cA
    @2
    @20
    wf
    wph
    vx
    cA
    @19
    @2
    @20
    wph
    @19
    @2
    wcel
    @7
    wph
    @19
    cB
    cW
    rfovd.b
    @19
    cB
    wss
    wph
    @18
    vy
    cB
    ssrab2
    a1i
    sselpwd
    adantr
    @20
    eqid
    fmptd
    wph
    @2
    cA
    @20
    cvv
    cV
    wph
    cB
    cW
    wcel
    #
    @2
    cvv
    wcel
    rfovd.b
    cB
    cW
    pwexg
    syl
    #
    rfovd.a
    elmapd
    mpbird
    adantr
    wph
    @9
    @3
    wcel
    #
    wa
    #
    @13
    @0
    cvv
    wph
    @0
    cvv
    wcel
    #
    @30
    wph
    cA
    cV
    wcel
    @28
    @32
    rfovd.a
    rfovd.b
    cA
    cB
    cV
    cW
    xpexg
    syl2anc
    adantr
    @31
    @13
    @7
    @8
    cB
    wcel
    #
    wa
    #
    wtru
    wa
    #
    vx
    vy
    copab
    @0
    @31
    @12
    @35
    vx
    vy
    @31
    @12
    @34
    wtru
    @31
    @7
    @11
    @33
    @31
    @7
    @10
    @2
    wcel
    #
    @11
    @33
    wi
    @31
    @7
    @36
    @31
    cA
    @2
    @6
    @9
    wph
    @30
    cA
    @2
    @9
    wf
    #
    wph
    @2
    cA
    @9
    cvv
    cV
    @29
    rfovd.a
    elmapd
    biimpa
    ffvelrnda
    ex
    @36
    @10
    cB
    @8
    @10
    cB
    elpwi
    sseld
    syl6
    imdistand
    @12
    wtru
    wi
    @31
    @12
    a1tru
    a1i
    jcad
    ssopab2dv
    wtru
    vx
    vy
    cA
    cB
    opabssxp
    syl6ss
    sselpwd
    wph
    @27
    @30
    wa
    #
    wa
    #
    @17
    @13
    wceq
    #
    @9
    @20
    wceq
    #
    @39
    @40
    wa
    #
    vu
    cA
    @9
    @20
    @42
    @30
    @9
    cA
    wfn
    wph
    @27
    @30
    @40
    simplrr
    @9
    @2
    cA
    elmapfn
    syl
    @42
    @28
    @19
    cvv
    wcel
    #
    vx
    cA
    wral
    @20
    cA
    wfn
    wph
    @28
    @38
    @40
    rfovd.b
    ad2antrr
    @28
    @43
    vx
    cA
    @18
    vy
    cB
    cW
    rabexg
    ralrimivw
    vx
    cA
    @19
    cvv
    vx
    cA
    nfcv
    fnmptf
    3syl
    @42
    vu
    cv
    #
    cA
    wcel
    #
    wa
    #
    @44
    @9
    cfv
    #
    @45
    vb
    cv
    #
    @47
    wcel
    #
    wa
    #
    vb
    cB
    crab
    #
    @44
    @20
    cfv
    @46
    cB
    @47
    cin
    #
    @49
    vb
    cB
    crab
    #
    @47
    @51
    vb
    cB
    @47
    dfin5
    @46
    @47
    cB
    wss
    @52
    @47
    wceq
    @46
    @47
    cB
    @46
    cA
    @2
    @44
    @9
    @46
    @30
    @37
    @46
    @27
    @30
    wph
    @38
    @40
    @45
    simpllr
    simprd
    @9
    @2
    cA
    elmapi
    syl
    @42
    @45
    simpr
    #
    ffvelrnd
    elpwid
    @47
    cB
    sseqin2
    sylib
    @45
    @53
    @51
    wceq
    @42
    @45
    @49
    @50
    vb
    cB
    @45
    @49
    ibar
    rabbidv
    adantl
    3eqtr3a
    @46
    va
    @44
    va
    cv
    #
    @48
    cop
    #
    @17
    wcel
    #
    vb
    cB
    crab
    #
    @51
    cA
    @20
    cvv
    @20
    va
    cA
    @58
    cmpt
    wceq
    @46
    vx
    va
    cA
    @19
    @58
    vx
    va
    weq
    #
    @19
    @6
    @48
    @17
    wbr
    #
    vb
    cB
    crab
    @58
    @18
    @60
    vy
    vb
    cB
    @8
    @48
    @6
    @17
    breq2
    cbvrabv
    @59
    @60
    @57
    vb
    cB
    @59
    @60
    @55
    @48
    @17
    wbr
    #
    @57
    @6
    @55
    @48
    @17
    breq1
    @55
    @48
    @17
    df-br
    syl6bb
    rabbidv
    syl5eq
    cbvmptv
    a1i
    @46
    va
    vu
    weq
    #
    wa
    #
    @57
    @50
    vb
    cB
    @63
    @57
    @44
    @48
    cop
    #
    @13
    wcel
    @50
    @63
    @56
    @64
    @17
    @13
    @63
    @55
    @44
    @48
    @46
    @62
    simpr
    opeq1d
    @39
    @40
    @45
    @62
    simpllr
    eleq12d
    @12
    @50
    vx
    vy
    @44
    @48
    vu
    vex
    #
    vb
    vex
    vx
    vu
    weq
    #
    vy
    vb
    weq
    #
    wa
    #
    @7
    @45
    @11
    @49
    @68
    @6
    @44
    cA
    @66
    @67
    simpl
    #
    eleq1d
    @68
    @8
    @48
    @10
    @47
    @66
    @67
    simpr
    @68
    @6
    @44
    @9
    @69
    fveq2d
    eleq12d
    anbi12d
    opelopaba
    syl6bb
    rabbidv
    @54
    @46
    @28
    @51
    cvv
    wcel
    wph
    @28
    @38
    @40
    @45
    rfovd.b
    ad3antrrr
    @50
    vb
    cB
    cW
    rabexg
    syl
    fvmptd
    eqtr4d
    eqfnfvd
    @39
    @41
    wa
    #
    @17
    wrel
    #
    @13
    wrel
    #
    @28
    @27
    wa
    #
    @41
    wa
    #
    @40
    @70
    @17
    cvv
    cvv
    cxp
    #
    wss
    @71
    @70
    @17
    @0
    @75
    @70
    @17
    @0
    wph
    @27
    @30
    @41
    simplrl
    elpwid
    cA
    cB
    xpss
    syl6ss
    @17
    df-rel
    sylibr
    @72
    @70
    @12
    vx
    vy
    relopab
    a1i
    @39
    @73
    @41
    wph
    @28
    @38
    @27
    rfovd.b
    @27
    @30
    simpl
    anim12i
    anim1i
    @74
    vu
    vv
    @17
    @13
    @44
    vv
    cv
    #
    cop
    #
    @13
    wcel
    @45
    @76
    @47
    wcel
    #
    wa
    #
    @74
    @77
    @17
    wcel
    #
    @12
    @79
    vx
    vy
    @44
    @76
    @65
    vv
    vex
    #
    @66
    vy
    vv
    weq
    #
    wa
    #
    @7
    @45
    @11
    @78
    @83
    @6
    @44
    cA
    @66
    @82
    simpl
    #
    eleq1d
    @83
    @8
    @76
    @10
    @47
    @66
    @82
    simpr
    @83
    @6
    @44
    @9
    @84
    fveq2d
    eleq12d
    anbi12d
    opelopaba
    @74
    @45
    @76
    @44
    @48
    @17
    wbr
    #
    vb
    cB
    crab
    #
    wcel
    #
    wa
    #
    @45
    @76
    cB
    wcel
    #
    @80
    wa
    #
    wa
    #
    @79
    @80
    @88
    @91
    wb
    @74
    @87
    @90
    @45
    @85
    @80
    vb
    @76
    cB
    vb
    vv
    weq
    @85
    @44
    @76
    @17
    wbr
    @80
    @48
    @76
    @44
    @17
    breq2
    @44
    @76
    @17
    df-br
    syl6bb
    elrab
    anbi2i
    a1i
    @74
    @45
    @78
    @87
    @74
    @45
    wa
    #
    @47
    @86
    @76
    @92
    va
    @44
    @61
    vb
    cB
    crab
    #
    @86
    cA
    @9
    cvv
    @92
    @9
    @20
    va
    cA
    @93
    cmpt
    @73
    @41
    @45
    simplr
    vx
    va
    cA
    @19
    @93
    @59
    @19
    @55
    @8
    @17
    wbr
    #
    vy
    cB
    crab
    @93
    @59
    @18
    @94
    vy
    cB
    @6
    @55
    @8
    @17
    breq1
    rabbidv
    @94
    @61
    vy
    vb
    cB
    @8
    @48
    @55
    @17
    breq2
    cbvrabv
    syl6eq
    cbvmptv
    syl6eq
    @62
    @93
    @86
    wceq
    @92
    @62
    @61
    @85
    vb
    cB
    @55
    @44
    @48
    @17
    breq1
    rabbidv
    adantl
    @74
    @45
    simpr
    @28
    @86
    cvv
    wcel
    @27
    @41
    @45
    @85
    vb
    cB
    cW
    rabexg
    ad3antrrr
    fvmptd
    eleq2d
    pm5.32da
    @74
    @17
    @0
    wss
    #
    @80
    @91
    wb
    @74
    @17
    @0
    @28
    @27
    @41
    simplr
    elpwid
    @95
    @80
    @45
    @80
    wa
    @91
    @95
    @80
    @45
    @80
    @44
    @17
    cdm
    #
    wcel
    @95
    @45
    @44
    @76
    @17
    @65
    @81
    opeldm
    @95
    @96
    cA
    @44
    @95
    @96
    @0
    cdm
    cA
    @17
    @0
    dmss
    cA
    cB
    dmxpss
    syl6ss
    sseld
    syl5
    pm4.71rd
    @95
    @80
    @90
    @45
    @95
    @80
    @89
    @80
    @76
    @17
    crn
    #
    wcel
    @95
    @89
    @44
    @76
    @17
    @65
    @81
    opelrn
    @95
    @97
    cB
    @76
    @95
    @97
    @0
    crn
    cB
    @17
    @0
    rnss
    cA
    cB
    rnxpss
    syl6ss
    sseld
    syl5
    pm4.71rd
    anbi2d
    bitrd
    syl
    3bitr4d
    syl5rbb
    eqrelrdv2
    syl21anc
    impbida
    f1ocnv2d
    wph
    cF
    @21
    wceq
    #
    @16
    @25
    wb
    wph
    cF
    cA
    cB
    cO
    co
    @21
    rfovcnvf1od.f
    wph
    vx
    vy
    cA
    cB
    cO
    cV
    cW
    vr
    va
    vb
    rfovd.rf
    rfovd.a
    rfovd.b
    rfovd
    syl5eq
    @98
    @4
    @22
    @15
    @24
    @1
    @3
    cF
    @21
    f1oeq1
    @98
    @5
    @23
    @14
    cF
    @21
    cnveq
    eqeq1d
    anbi12d
    syl
    mpbird
end
