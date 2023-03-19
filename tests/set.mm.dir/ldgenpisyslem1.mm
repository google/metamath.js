include "cv.mm"
include "cin.mm"
include "wcel.mm"
include "cpw.mm"
include "crab.mm"
include "c0.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "wss.mm"
include "ssrab2.mm"
include "cvv.mm"
include "wb.mm"
include "pwexg.mm"
include "rabexg.mm"
include "elpwg.mm"
include "4syl.mm"
include "mpbiri.mm"
include "0elpw.mm"
include "a1i.mm"
include "cint.mm"
include "isldsys.mm"
include "simprbi.mm"
include "simp1d.mm"
include "ad2antlr.mm"
include "ex.mm"
include "ralrimiva.mm"
include "0ex.mm"
include "elintrab.mm"
include "sylibr.mm"
include "in0.mm"
include "3eltr4g.mm"
include "wceq.mm"
include "ineq2.mm"
include "eleq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "pwidg.mm"
include "syl.mm"
include "adantr.mm"
include "elpwdifcl.mm"
include "cun.mm"
include "pwldsys.mm"
include "cfi.mm"
include "cfv.mm"
include "ispisys.mm"
include "sylib.mm"
include "simpld.mm"
include "elpwid.mm"
include "sseq2.mm"
include "intminss.mm"
include "syl2anc.mm"
include "syl5eqss.mm"
include "sseldd.mm"
include "ad3antrrr.mm"
include "difin.mm"
include "difin2.mm"
include "syl5eq.mm"
include "incom.mm"
include "syl6eq.mm"
include "difuncomp.mm"
include "eqtr3d.mm"
include "difeq2.mm"
include "simp2d.mm"
include "cbvralv.mm"
include "simplr.mm"
include "syl6eleq.mm"
include "elintrabg.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "imp.mm"
include "adantllr.mm"
include "simpr.mm"
include "rspcdva.mm"
include "simpllr.mm"
include "simprd.mm"
include "vex.mm"
include "inex2.mm"
include "mp1i.mm"
include "rspa.mm"
include "syl21anc.mm"
include "inss1.mm"
include "disjdif.mm"
include "ssdisj.mm"
include "mp2an.mm"
include "eqtri.mm"
include "unelldsys.mm"
include "eqeltrd.mm"
include "inex1g.mm"
include "mpbird.mm"
include "syl6eleqr.mm"
include "jca.mm"
include "sylan2b.mm"
include "ad2antrr.mm"
include "sspwb.mm"
include "mpbi.mm"
include "sseldi.mm"
include "elpwunicl.mm"
include "cmpt.mm"
include "crn.mm"
include "ciun.mm"
include "uniin2.mm"
include "dfiun3.mm"
include "eqtr3i.mm"
include "nfv.mm"
include "nfdisj1.mm"
include "nfan.mm"
include "elpwi.mm"
include "ad4antlr.mm"
include "sselda.mm"
include "eleq2i.mm"
include "bitri.mm"
include "sylanb.mm"
include "ralrimi.mm"
include "eqid.mm"
include "rnmptss.mm"
include "sselpwd.mm"
include "1stcrestlem.mm"
include "disjin2.mm"
include "disjrnmpt.mm"
include "3syl.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfcv.mm"
include "id.mm"
include "cbvdisjf.mm"
include "breq1.mm"
include "disjeq1f.mm"
include "anbi12d.mm"
include "unieq.mm"
include "imbi12d.mm"
include "simp3d.mm"
include "disjeq1.mm"
include "syl22anc.mm"
include "syl5eqel.mm"
include "vuniex.mm"
include "3jca.mm"

theorem ldgenpisyslem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cP: class P
  let cT: class T
  let cE: class E
  let cL: class L
  let cO: class O
  let cV: class V
  let vs: setvar s
  let vb: setvar b
  let vz: setvar z
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let vu: setvar u
  let cS: class S
  assume dynkin.p: |- P = { s e. ~P ~P O | ( fi ` s ) C_ s }
  assume dynkin.l: |- L = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s ( O \ x ) e. s /\ A. x e. ~P s ( ( x ~<_ _om /\ Disj_ y e. x y ) -> U. x e. s ) ) }
  assume dynkin.o: |- ( ph -> O e. V )
  assume ldgenpisys.e: |- E = |^| { t e. L | T C_ t }
  assume ldgenpisys.1: |- ( ph -> T e. P )
  assume ldgenpisyslem1.1: |- ( ph -> A e. E )

  disjoint b s
  disjoint b x
  disjoint s x
  disjoint A b
  disjoint A s
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint b t
  disjoint b y
  disjoint s t
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint E b
  disjoint E s
  disjoint E t
  disjoint E x
  disjoint E y
  disjoint O b
  disjoint O t
  disjoint O y
  disjoint V x
  disjoint T y
  disjoint ph y
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint t x
  disjoint t y
  disjoint x y
  disjoint L t
  disjoint L x
  disjoint L y
  disjoint O s
  disjoint O t
  disjoint O x
  disjoint P t
  disjoint P x
  disjoint P y
  disjoint L s
  disjoint T s
  disjoint T t
  disjoint T x
  disjoint ph t
  disjoint ph x
  disjoint A z
  disjoint b z
  disjoint s z
  disjoint t z
  disjoint x z
  disjoint y z
  disjoint L z
  disjoint f i
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint i n
  disjoint i s
  disjoint i t
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint s z
  disjoint t z
  disjoint x z
  disjoint y z
  disjoint L f
  disjoint L i
  disjoint L n
  disjoint P f
  disjoint P i
  disjoint P n
  disjoint L u
  disjoint s u
  disjoint t u
  disjoint u x
  disjoint O u
  disjoint S t
  disjoint T u
  assert |- ( ph -> { b e. ~P O | ( A i^i b ) e. E } e. L )

  proof
    wph
    cA
    vb
    cv
    #
    cin
    #
    cE
    wcel
    #
    vb
    cO
    cpw
    #
    crab
    #
    @3
    cpw
    #
    wcel
    #
    c0
    @4
    wcel
    #
    cO
    vx
    cv
    #
    cdif
    #
    @4
    wcel
    #
    vx
    @4
    wral
    #
    @8
    com
    cdom
    wbr
    #
    vy
    @8
    vy
    cv
    #
    wdisj
    #
    wa
    #
    @8
    cuni
    #
    @4
    wcel
    #
    wi
    #
    vx
    @4
    cpw
    #
    wral
    #
    w3a
    @4
    cL
    wcel
    wph
    @6
    @4
    @3
    wss
    #
    @2
    vb
    @3
    ssrab2
    #
    wph
    cO
    cV
    wcel
    #
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @6
    @21
    wb
    dynkin.o
    cO
    cV
    pwexg
    @2
    vb
    @3
    cvv
    rabexg
    @4
    @3
    cvv
    elpwg
    4syl
    mpbiri
    wph
    @7
    @11
    @20
    wph
    c0
    @3
    wcel
    #
    cA
    c0
    cin
    #
    cE
    wcel
    #
    @7
    @24
    wph
    cO
    0elpw
    a1i
    wph
    c0
    cT
    vt
    cv
    #
    wss
    #
    vt
    cL
    crab
    cint
    #
    @25
    cE
    wph
    @28
    c0
    @27
    wcel
    #
    wi
    #
    vt
    cL
    wral
    c0
    @29
    wcel
    wph
    @31
    vt
    cL
    wph
    @27
    cL
    wcel
    #
    wa
    #
    @28
    @30
    @32
    @30
    wph
    @28
    @32
    @30
    @9
    @27
    wcel
    #
    vx
    @27
    wral
    #
    @15
    @16
    @27
    wcel
    #
    wi
    #
    vx
    @27
    cpw
    #
    wral
    #
    @32
    @27
    @5
    wcel
    @30
    @35
    @39
    w3a
    vx
    vy
    @27
    cL
    cO
    vs
    dynkin.l
    isldsys
    simprbi
    #
    simp1d
    ad2antlr
    ex
    ralrimiva
    @28
    vt
    c0
    cL
    0ex
    elintrab
    sylibr
    cA
    in0
    ldgenpisys.e
    3eltr4g
    @2
    @26
    vb
    c0
    @3
    @0
    c0
    wceq
    @1
    @25
    cE
    @0
    c0
    cA
    ineq2
    eleq1d
    elrab
    sylanbrc
    wph
    @10
    vx
    @4
    wph
    @8
    @4
    wcel
    #
    wa
    @9
    @3
    wcel
    #
    cA
    @9
    cin
    #
    cE
    wcel
    #
    wa
    #
    @10
    @41
    wph
    @8
    @3
    wcel
    #
    cA
    @8
    cin
    #
    cE
    wcel
    #
    wa
    #
    @45
    @2
    @48
    vb
    @8
    @3
    @0
    @8
    wceq
    @1
    @47
    cE
    @0
    @8
    cA
    ineq2
    eleq1d
    elrab
    wph
    @49
    wa
    #
    @42
    @44
    @50
    cO
    @8
    cO
    wph
    cO
    @3
    wcel
    #
    @49
    wph
    @23
    @51
    dynkin.o
    cO
    cV
    pwidg
    syl
    adantr
    elpwdifcl
    @50
    @43
    @29
    cE
    @50
    @43
    @29
    wcel
    #
    @28
    @43
    @27
    wcel
    #
    wi
    #
    vt
    cL
    wral
    #
    @50
    @54
    vt
    cL
    @50
    @32
    wa
    #
    @28
    @53
    @56
    @28
    wa
    #
    @43
    cO
    cO
    cA
    cdif
    #
    @47
    cun
    #
    cdif
    #
    @27
    @57
    cA
    cO
    wss
    #
    @43
    @60
    wceq
    wph
    @61
    @49
    @32
    @28
    wph
    cA
    cO
    wph
    cE
    @3
    cA
    wph
    cE
    @29
    @3
    ldgenpisys.e
    wph
    @3
    cL
    wcel
    #
    cT
    @3
    wss
    #
    @29
    @3
    wss
    wph
    @23
    @62
    dynkin.o
    vx
    vy
    cL
    cO
    cV
    vs
    dynkin.l
    pwldsys
    syl
    wph
    cT
    @3
    wph
    cT
    @5
    wcel
    #
    cT
    cfi
    cfv
    cT
    wss
    #
    wph
    cT
    cP
    wcel
    @64
    @65
    wa
    ldgenpisys.1
    cP
    cT
    cO
    vs
    dynkin.p
    ispisys
    sylib
    simpld
    elpwid
    @28
    @63
    vt
    @3
    cL
    @27
    @3
    cT
    sseq2
    intminss
    syl2anc
    syl5eqss
    ldgenpisyslem1.1
    sseldd
    elpwid
    ad3antrrr
    @61
    cA
    @47
    cdif
    #
    @43
    @60
    @61
    @66
    @9
    cA
    cin
    #
    @43
    @61
    @66
    cA
    @8
    cdif
    @67
    cA
    @8
    difin
    cA
    @8
    cO
    difin2
    syl5eq
    @9
    cA
    incom
    syl6eq
    cA
    @47
    cO
    difuncomp
    eqtr3d
    syl
    @57
    cO
    @13
    cdif
    #
    @27
    wcel
    #
    @60
    @27
    wcel
    vy
    @27
    @59
    @13
    @59
    wceq
    @68
    @60
    @27
    @13
    @59
    cO
    difeq2
    eleq1d
    @57
    @35
    @69
    vy
    @27
    wral
    @32
    @35
    @50
    @28
    @32
    @30
    @35
    @39
    @40
    simp2d
    #
    ad2antlr
    @34
    @69
    vx
    vy
    @27
    @8
    @13
    wceq
    @9
    @68
    @27
    @8
    @13
    cO
    difeq2
    eleq1d
    cbvralv
    sylib
    @57
    vx
    vy
    @58
    @47
    @27
    cL
    cO
    vs
    dynkin.l
    @50
    @32
    @28
    simplr
    #
    @57
    @32
    cA
    @27
    wcel
    #
    @58
    @27
    wcel
    #
    @71
    wph
    @32
    @28
    @72
    @49
    @33
    @28
    @72
    wph
    @28
    @72
    wi
    #
    vt
    cL
    wph
    cA
    @29
    wcel
    #
    @74
    vt
    cL
    wral
    #
    wph
    cA
    cE
    @29
    ldgenpisyslem1.1
    ldgenpisys.e
    syl6eleq
    wph
    cA
    cE
    wcel
    #
    @75
    @76
    wb
    ldgenpisyslem1.1
    @28
    vt
    cA
    cL
    cE
    elintrabg
    syl
    mpbid
    r19.21bi
    imp
    adantllr
    @32
    @72
    wa
    @34
    @73
    vx
    @27
    cA
    @8
    cA
    wceq
    @9
    @58
    @27
    @8
    cA
    cO
    difeq2
    eleq1d
    @32
    @35
    @72
    @70
    adantr
    @32
    @72
    simpr
    rspcdva
    syl2anc
    @57
    @28
    @47
    @27
    wcel
    #
    wi
    #
    vt
    cL
    wral
    #
    @32
    @28
    @78
    @57
    @47
    @29
    wcel
    #
    @80
    @57
    @47
    cE
    @29
    @57
    @46
    @48
    wph
    @49
    @32
    @28
    simpllr
    simprd
    ldgenpisys.e
    syl6eleq
    @47
    cvv
    wcel
    @81
    @80
    wb
    @57
    @8
    cA
    vx
    vex
    inex2
    @28
    vt
    @47
    cL
    cvv
    elintrabg
    mp1i
    mpbid
    @71
    @56
    @28
    simpr
    @80
    @32
    wa
    @28
    @78
    @79
    vt
    cL
    rspa
    imp
    syl21anc
    @58
    @47
    cin
    #
    c0
    wceq
    @57
    @82
    @47
    @58
    cin
    #
    c0
    @58
    @47
    incom
    @47
    cA
    wss
    cA
    @58
    cin
    c0
    wceq
    @83
    c0
    wceq
    cA
    @8
    inss1
    cA
    cO
    disjdif
    @47
    cA
    @58
    ssdisj
    mp2an
    eqtri
    a1i
    unelldsys
    rspcdva
    eqeltrd
    ex
    ralrimiva
    @50
    @43
    cvv
    wcel
    #
    @52
    @55
    wb
    wph
    @84
    @49
    wph
    @77
    @84
    ldgenpisyslem1.1
    cA
    @9
    cE
    inex1g
    syl
    adantr
    @28
    vt
    @43
    cL
    cvv
    elintrabg
    syl
    mpbird
    ldgenpisys.e
    syl6eleqr
    jca
    sylan2b
    @2
    @44
    vb
    @9
    @3
    @0
    @9
    wceq
    @1
    @43
    cE
    @0
    @9
    cA
    ineq2
    eleq1d
    elrab
    sylibr
    ralrimiva
    wph
    @18
    vx
    @19
    wph
    @8
    @19
    wcel
    #
    wa
    #
    @15
    @17
    @86
    @15
    wa
    #
    @16
    @3
    wcel
    cA
    @16
    cin
    #
    cE
    wcel
    #
    @17
    @87
    @8
    cO
    cV
    wph
    @23
    @85
    @15
    dynkin.o
    ad2antrr
    @87
    @19
    @5
    @8
    @21
    @19
    @5
    wss
    @22
    @4
    @3
    sspwb
    mpbi
    wph
    @85
    @15
    simplr
    sseldi
    elpwunicl
    @87
    @88
    @29
    cE
    @87
    @28
    @88
    @27
    wcel
    #
    wi
    #
    vt
    cL
    wral
    @88
    @29
    wcel
    @87
    @91
    vt
    cL
    @87
    @32
    wa
    #
    @28
    @90
    @92
    @28
    wa
    #
    @88
    vy
    @8
    cA
    @13
    cin
    #
    cmpt
    #
    crn
    #
    cuni
    #
    @27
    vy
    @8
    @94
    ciun
    @88
    @97
    vy
    cA
    @8
    uniin2
    vy
    @8
    @94
    @13
    cA
    vy
    vex
    inex2
    #
    dfiun3
    eqtr3i
    @93
    @32
    @96
    @38
    wcel
    #
    @96
    com
    cdom
    wbr
    #
    vy
    @96
    @13
    wdisj
    #
    @97
    @27
    wcel
    #
    @87
    @32
    @28
    simplr
    #
    @93
    @96
    @27
    cL
    @103
    @93
    @94
    @27
    wcel
    #
    vy
    @8
    wral
    @96
    @27
    wss
    @93
    @104
    vy
    @8
    @92
    @28
    vy
    @87
    @32
    vy
    @86
    @15
    vy
    @86
    vy
    nfv
    @12
    @14
    vy
    @12
    vy
    nfv
    vy
    @8
    @13
    nfdisj1
    nfan
    nfan
    @32
    vy
    nfv
    nfan
    @28
    vy
    nfv
    nfan
    @93
    @13
    @8
    wcel
    #
    @104
    @93
    @105
    wa
    #
    @94
    cE
    wcel
    #
    @32
    @28
    @104
    @106
    @13
    @4
    wcel
    #
    @107
    @93
    @8
    @4
    @13
    @85
    @8
    @4
    wss
    wph
    @15
    @32
    @28
    @8
    @4
    elpwi
    ad4antlr
    sselda
    @108
    @13
    @3
    wcel
    @107
    @2
    @107
    vb
    @13
    @3
    @0
    @13
    wceq
    @1
    @94
    cE
    @0
    @13
    cA
    ineq2
    eleq1d
    elrab
    simprbi
    syl
    @87
    @32
    @28
    @105
    simpllr
    @92
    @28
    @105
    simplr
    @107
    @32
    wa
    @28
    @104
    @107
    @28
    @104
    wi
    #
    vt
    cL
    wral
    #
    @32
    @109
    @107
    @94
    @29
    wcel
    @110
    cE
    @29
    @94
    ldgenpisys.e
    eleq2i
    @28
    vt
    @94
    cL
    @98
    elintrab
    bitri
    @109
    vt
    cL
    rspa
    sylanb
    imp
    syl21anc
    ex
    ralrimi
    vy
    @8
    @94
    @27
    @95
    @95
    eqid
    rnmptss
    syl
    sselpwd
    @93
    @12
    @100
    @93
    @12
    @14
    @86
    @15
    @32
    @28
    simpllr
    #
    simpld
    vy
    @8
    @94
    1stcrestlem
    syl
    @93
    vz
    @96
    vz
    cv
    #
    wdisj
    #
    @101
    @93
    @14
    vy
    @8
    @94
    wdisj
    @113
    @93
    @12
    @14
    @111
    simprd
    vy
    cA
    @8
    @13
    disjin2
    vy
    vz
    @8
    @94
    disjrnmpt
    3syl
    vy
    vz
    @96
    @13
    @112
    vy
    @95
    vy
    @8
    @94
    nfmpt1
    nfrn
    #
    vz
    @13
    nfcv
    vy
    @112
    nfcv
    #
    @13
    @112
    wceq
    id
    cbvdisjf
    sylibr
    @32
    @99
    wa
    #
    @100
    @101
    wa
    #
    @102
    @116
    @112
    com
    cdom
    wbr
    #
    vy
    @112
    @13
    wdisj
    #
    wa
    #
    @112
    cuni
    #
    @27
    wcel
    #
    wi
    #
    @117
    @102
    wi
    vz
    @38
    @96
    @112
    @96
    wceq
    #
    @120
    @117
    @122
    @102
    @124
    @118
    @100
    @119
    @101
    @112
    @96
    com
    cdom
    breq1
    vy
    @112
    @96
    @13
    @115
    @114
    disjeq1f
    anbi12d
    @124
    @121
    @97
    @27
    @112
    @96
    unieq
    eleq1d
    imbi12d
    @32
    @123
    vz
    @38
    wral
    #
    @99
    @32
    @39
    @125
    @32
    @30
    @35
    @39
    @40
    simp3d
    @37
    @123
    vx
    vz
    @38
    @8
    @112
    wceq
    #
    @15
    @120
    @36
    @122
    @126
    @12
    @118
    @14
    @119
    @8
    @112
    com
    cdom
    breq1
    vy
    @8
    @112
    @13
    disjeq1
    anbi12d
    @126
    @16
    @121
    @27
    @8
    @112
    unieq
    eleq1d
    imbi12d
    cbvralv
    sylib
    adantr
    @32
    @99
    simpr
    rspcdva
    imp
    syl22anc
    syl5eqel
    ex
    ralrimiva
    @28
    vt
    @88
    cL
    @16
    cA
    vx
    vuniex
    inex2
    elintrab
    sylibr
    ldgenpisys.e
    syl6eleqr
    @2
    @89
    vb
    @16
    @3
    @0
    @16
    wceq
    @1
    @88
    cE
    @0
    @16
    cA
    ineq2
    eleq1d
    elrab
    sylanbrc
    ex
    ralrimiva
    3jca
    vx
    vy
    @4
    cL
    cO
    vs
    dynkin.l
    isldsys
    sylanbrc
end
