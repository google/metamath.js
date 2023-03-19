include "ctop.mm"
include "wcel.mm"
include "ccmp.mm"
include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "cptfin.mm"
include "wrex.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "elpwi.mm"
include "w3a.mm"
include "cfn.mm"
include "cin.mm"
include "cmpcov.mm"
include "elfpw.mm"
include "finptfin.mm"
include "anim1i.mm"
include "anassrs.mm"
include "ancom1s.mm"
include "sylanb.mm"
include "reximi2.mm"
include "syl.mm"
include "3exp.mm"
include "syl5.mm"
include "ralrimiv.mm"
include "c0.mm"
include "0elpw.mm"
include "0fin.mm"
include "elin.mm"
include "mpbir2an.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mpan.mm"
include "a1d.mm"
include "a1i.mm"
include "wne.mm"
include "wex.mm"
include "n0.mm"
include "simp2.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "eluni2.mm"
include "syl6ib.mm"
include "cun.mm"
include "cmpt.mm"
include "crn.mm"
include "ciun.mm"
include "simpl3.mm"
include "simprl.mm"
include "sseldd.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "ralrimivw.mm"
include "iunss.mm"
include "sylibr.mm"
include "ssequn1.mm"
include "sylib.mm"
include "simpl2.mm"
include "uniiun.mm"
include "uneq2d.mm"
include "eqtr3d.mm"
include "iunun.mm"
include "vex.mm"
include "unex.mm"
include "dfiun3.mm"
include "eqtr3i.mm"
include "wf.mm"
include "simpll1.mm"
include "adantr.mm"
include "sselda.mm"
include "unopn.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "wb.mm"
include "elpw2g.mm"
include "3ad2ant1.mm"
include "mpbird.mm"
include "sseq2.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpid.mm"
include "crab.mm"
include "simprr.mm"
include "ssel2.mm"
include "3ad2antl3.mm"
include "adantrr.mm"
include "elunii.mm"
include "syl2anc.mm"
include "syl6eleqr.mm"
include "eleqtrd.mm"
include "ptfinfin.mm"
include "expcom.mm"
include "elun1.mm"
include "ad2antll.mm"
include "cvv.mm"
include "rgenw.mm"
include "eleq2.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "ssralv.mm"
include "sylc.mm"
include "rabid2.mm"
include "eleq1d.mm"
include "biimprd.mm"
include "cfv.mm"
include "cab.mm"
include "rnmpt.mm"
include "syl6sseq.mm"
include "ssabral.mm"
include "uneq2.mm"
include "ac6sfi.mm"
include "csn.mm"
include "ad2antrr.mm"
include "snssd.mm"
include "unssd.mm"
include "wfo.mm"
include "wfn.mm"
include "simprrl.mm"
include "ffn.mm"
include "dffn4.mm"
include "fofi.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "sylanbrc.mm"
include "simplrr.mm"
include "simprrr.mm"
include "iuneq2.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "ssun2.mm"
include "vsnid.mm"
include "sselii.mm"
include "fvssunirn.mm"
include "ssun1.mm"
include "unissi.mm"
include "sstri.mm"
include "unssi.mm"
include "mpbir.mm"
include "syl6eqss.mm"
include "sstrd.mm"
include "uniss.mm"
include "eqssd.mm"
include "expr.mm"
include "exlimdv.mm"
include "ex.mm"
include "mpdd.mm"
include "3syld.mm"
include "com23.mm"
include "rexlimdv.mm"
include "syld.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "pm2.61dne.mm"
include "syl3an3.mm"
include "com24.mm"
include "ralrimdv.mm"
include "iscmp.mm"
include "baibr.mm"
include "sylibd.mm"
include "impbid2.mm"

theorem comppfsc
  let cJ: class J
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vz: setvar z
  assume comppfsc.1: |- X = U. J

  disjoint c d
  disjoint J c
  disjoint J d
  disjoint X c
  disjoint X d
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a p
  disjoint a q
  disjoint a s
  disjoint a x
  disjoint a z
  disjoint J a
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b p
  disjoint b q
  disjoint b s
  disjoint b x
  disjoint b z
  disjoint J b
  disjoint c f
  disjoint c p
  disjoint c q
  disjoint c s
  disjoint c x
  disjoint c z
  disjoint d f
  disjoint d p
  disjoint d q
  disjoint d s
  disjoint d x
  disjoint d z
  disjoint f p
  disjoint f q
  disjoint f s
  disjoint f x
  disjoint f z
  disjoint J f
  disjoint p q
  disjoint p s
  disjoint p x
  disjoint p z
  disjoint J p
  disjoint q s
  disjoint q x
  disjoint q z
  disjoint J q
  disjoint s x
  disjoint s z
  disjoint J s
  disjoint x z
  disjoint J x
  disjoint J z
  disjoint X a
  disjoint X b
  disjoint X f
  disjoint X p
  disjoint X q
  disjoint X s
  disjoint X x
  disjoint X z
  assert |- ( J e. Top -> ( J e. Comp <-> A. c e. ~P J ( X = U. c -> E. d e. PtFin ( d C_ c /\ X = U. d ) ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    ccmp
    wcel
    #
    cX
    vc
    cv
    #
    cuni
    #
    wceq
    #
    vd
    cv
    #
    @2
    wss
    #
    cX
    @5
    cuni
    #
    wceq
    #
    wa
    #
    vd
    cptfin
    wrex
    #
    wi
    #
    vc
    cJ
    cpw
    #
    wral
    #
    @1
    @11
    vc
    @12
    @2
    @12
    wcel
    @2
    cJ
    wss
    #
    @1
    @11
    @2
    cJ
    elpwi
    @1
    @14
    @4
    @10
    @1
    @14
    @4
    w3a
    @8
    vd
    @2
    cpw
    cfn
    cin
    #
    wrex
    @10
    @2
    cJ
    cX
    vd
    comppfsc.1
    cmpcov
    @8
    @9
    vd
    @15
    cptfin
    @5
    @15
    wcel
    @6
    @5
    cfn
    wcel
    #
    wa
    @8
    @5
    cptfin
    wcel
    #
    @9
    wa
    #
    @5
    @2
    elfpw
    @16
    @6
    @8
    @18
    @16
    @6
    @8
    @18
    @16
    @17
    @9
    @5
    finptfin
    anim1i
    anassrs
    ancom1s
    sylanb
    reximi2
    syl
    3exp
    syl5
    ralrimiv
    @0
    @13
    cX
    va
    cv
    #
    cuni
    #
    wceq
    #
    cX
    vb
    cv
    #
    cuni
    #
    wceq
    #
    vb
    @19
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    va
    @12
    wral
    #
    @1
    @0
    @13
    @28
    va
    @12
    @0
    @21
    @19
    @12
    wcel
    #
    @13
    @27
    @0
    @21
    @30
    @13
    @27
    wi
    #
    @30
    @0
    @21
    @19
    cJ
    wss
    #
    @31
    @19
    cJ
    elpwi
    @0
    @21
    @32
    w3a
    #
    @31
    cX
    c0
    cX
    c0
    wceq
    #
    @31
    wi
    @33
    @34
    @27
    @13
    c0
    @26
    wcel
    #
    @34
    @27
    @35
    c0
    @25
    wcel
    c0
    cfn
    wcel
    @19
    0elpw
    0fin
    c0
    @25
    cfn
    elin
    mpbir2an
    @24
    @34
    vb
    c0
    @26
    @22
    c0
    wceq
    #
    @23
    c0
    cX
    @36
    @23
    c0
    cuni
    c0
    @22
    c0
    unieq
    uni0
    syl6eq
    eqeq2d
    rspcev
    mpan
    a1d
    a1i
    cX
    c0
    wne
    vx
    cv
    #
    cX
    wcel
    #
    vx
    wex
    @33
    @31
    vx
    cX
    n0
    @33
    @38
    @31
    vx
    @33
    @38
    @37
    vs
    cv
    #
    wcel
    #
    vs
    @19
    wrex
    #
    @31
    @33
    @38
    @37
    @20
    wcel
    #
    @41
    @33
    @38
    @42
    @33
    cX
    @20
    @37
    @0
    @21
    @32
    simp2
    eleq2d
    biimpd
    vs
    @37
    @19
    eluni2
    syl6ib
    @33
    @40
    @31
    vs
    @19
    @33
    @39
    @19
    wcel
    #
    @40
    wa
    #
    wa
    #
    @13
    @5
    vp
    @19
    @39
    vp
    cv
    #
    cun
    #
    cmpt
    #
    crn
    #
    wss
    #
    @8
    wa
    #
    vd
    cptfin
    wrex
    #
    @27
    @45
    @13
    cX
    @49
    cuni
    #
    wceq
    #
    @52
    @45
    cX
    vp
    @19
    @39
    ciun
    #
    vp
    @19
    @46
    ciun
    #
    cun
    #
    @53
    @45
    @55
    cX
    cun
    #
    cX
    @57
    @45
    @55
    cX
    wss
    #
    @58
    cX
    wceq
    @45
    @39
    cX
    wss
    #
    vp
    @19
    wral
    @59
    @45
    @60
    vp
    @19
    @45
    @39
    cJ
    wcel
    #
    @60
    @45
    @19
    cJ
    @39
    @0
    @21
    @32
    @44
    simpl3
    #
    @33
    @43
    @40
    simprl
    #
    sseldd
    #
    @61
    @39
    cJ
    cuni
    #
    cX
    @39
    cJ
    elssuni
    comppfsc.1
    syl6sseqr
    syl
    ralrimivw
    vp
    @19
    @39
    cX
    iunss
    sylibr
    @55
    cX
    ssequn1
    sylib
    @45
    cX
    @56
    @55
    @45
    cX
    @20
    @56
    @0
    @21
    @32
    @44
    simpl2
    vp
    @19
    uniiun
    syl6eq
    uneq2d
    eqtr3d
    vp
    @19
    @47
    ciun
    @57
    @53
    vp
    @19
    @39
    @46
    iunun
    vp
    @19
    @47
    @39
    @46
    vs
    vex
    vp
    vex
    unex
    #
    dfiun3
    eqtr3i
    syl6eq
    @45
    @49
    @12
    wcel
    #
    @13
    @54
    @52
    wi
    #
    wi
    @45
    @67
    @49
    cJ
    wss
    #
    @45
    @19
    cJ
    @48
    wf
    @69
    @45
    vp
    @19
    @47
    cJ
    @48
    @45
    @46
    @19
    wcel
    #
    wa
    @0
    @61
    @46
    cJ
    wcel
    @47
    cJ
    wcel
    @0
    @21
    @32
    @44
    @70
    simpll1
    @45
    @61
    @70
    @64
    adantr
    @45
    @19
    cJ
    @46
    @62
    sselda
    @39
    @46
    cJ
    unopn
    syl3anc
    @48
    eqid
    #
    fmptd
    @19
    cJ
    @48
    frn
    syl
    @33
    @67
    @69
    wb
    #
    @44
    @0
    @21
    @72
    @32
    @49
    cJ
    ctop
    elpw2g
    3ad2ant1
    adantr
    mpbird
    @11
    @68
    vc
    @49
    @12
    @2
    @49
    wceq
    #
    @4
    @54
    @10
    @52
    @73
    @3
    @53
    cX
    @2
    @49
    unieq
    eqeq2d
    @73
    @9
    @51
    vd
    cptfin
    @73
    @6
    @50
    @8
    @2
    @49
    @5
    sseq2
    anbi1d
    rexbidv
    imbi12d
    rspcv
    syl
    mpid
    @45
    @51
    @27
    vd
    cptfin
    @45
    @51
    @17
    @27
    @45
    @51
    @17
    @27
    wi
    @45
    @51
    wa
    #
    @17
    @37
    vz
    cv
    #
    wcel
    #
    vz
    @5
    crab
    #
    cfn
    wcel
    #
    @16
    @27
    @74
    @37
    @7
    wcel
    #
    @17
    @78
    wi
    @74
    @37
    cX
    @7
    @45
    @38
    @51
    @45
    @37
    @65
    cX
    @45
    @40
    @61
    @37
    @65
    wcel
    @33
    @43
    @40
    simprr
    @33
    @43
    @61
    @40
    @32
    @0
    @43
    @61
    @21
    @19
    cJ
    @39
    ssel2
    3ad2antl3
    adantrr
    @37
    @39
    cJ
    elunii
    syl2anc
    comppfsc.1
    syl6eleqr
    adantr
    @45
    @50
    @8
    simprr
    eleqtrd
    @17
    @79
    @78
    vz
    @5
    @37
    @7
    @7
    eqid
    ptfinfin
    expcom
    syl
    @74
    @16
    @78
    @74
    @5
    @77
    cfn
    @74
    @76
    vz
    @5
    wral
    #
    @5
    @77
    wceq
    @74
    @50
    @76
    vz
    @49
    wral
    #
    @80
    @45
    @50
    @8
    simprl
    #
    @45
    @81
    @51
    @45
    @37
    @47
    wcel
    #
    vp
    @19
    wral
    #
    @81
    @45
    @83
    vp
    @19
    @40
    @83
    @33
    @43
    @37
    @39
    @46
    elun1
    ad2antll
    ralrimivw
    @47
    cvv
    wcel
    #
    vp
    @19
    wral
    @81
    @84
    wb
    @85
    vp
    @19
    @66
    rgenw
    @76
    @83
    vp
    vz
    @19
    @47
    @48
    cvv
    @71
    @75
    @47
    @37
    eleq2
    ralrnmpt
    ax-mp
    sylibr
    adantr
    @76
    vz
    @5
    @49
    ssralv
    sylc
    @76
    vz
    @5
    rabid2
    sylibr
    eleq1d
    biimprd
    @74
    @16
    @5
    @19
    vf
    cv
    #
    wf
    #
    vq
    cv
    #
    @39
    @88
    @86
    cfv
    #
    cun
    #
    wceq
    #
    vq
    @5
    wral
    #
    wa
    #
    vf
    wex
    #
    @27
    @74
    @88
    @47
    wceq
    #
    vp
    @19
    wrex
    #
    vq
    @5
    wral
    #
    @16
    @94
    wi
    @74
    @5
    @96
    vq
    cab
    #
    wss
    @97
    @74
    @5
    @49
    @98
    @82
    vp
    vq
    @19
    @47
    @48
    @71
    rnmpt
    syl6sseq
    @96
    vq
    @5
    ssabral
    sylib
    @16
    @97
    @94
    @95
    @91
    vq
    vp
    @5
    @19
    vf
    @46
    @89
    wceq
    @47
    @90
    @88
    @46
    @89
    @39
    uneq2
    eqeq2d
    ac6sfi
    expcom
    syl
    @74
    @16
    @94
    @27
    wi
    @74
    @16
    wa
    @93
    @27
    vf
    @74
    @16
    @93
    @27
    @74
    @16
    @93
    wa
    #
    wa
    #
    @86
    crn
    #
    @39
    csn
    #
    cun
    #
    @26
    wcel
    #
    cX
    @103
    cuni
    #
    wceq
    #
    @27
    @100
    @103
    @19
    wss
    @103
    cfn
    wcel
    #
    @104
    @100
    @101
    @102
    @19
    @93
    @101
    @19
    wss
    #
    @74
    @16
    @87
    @108
    @92
    @5
    @19
    @86
    frn
    adantr
    ad2antll
    #
    @100
    @39
    @19
    @45
    @43
    @51
    @99
    @63
    ad2antrr
    snssd
    unssd
    @100
    @101
    cfn
    wcel
    #
    @102
    cfn
    wcel
    @107
    @100
    @16
    @5
    @101
    @86
    wfo
    #
    @110
    @74
    @16
    @93
    simprl
    @100
    @86
    @5
    wfn
    #
    @111
    @100
    @87
    @112
    @74
    @16
    @87
    @92
    simprrl
    @5
    @19
    @86
    ffn
    syl
    @5
    @86
    dffn4
    sylib
    @5
    @101
    @86
    fofi
    syl2anc
    @39
    snfi
    @101
    @102
    unfi
    sylancl
    @103
    @19
    elfpw
    sylanbrc
    @100
    cX
    @105
    @100
    cX
    vq
    @5
    @90
    ciun
    #
    @105
    @100
    cX
    @7
    @113
    @45
    @50
    @8
    @99
    simplrr
    @100
    @7
    vq
    @5
    @88
    ciun
    #
    @113
    vq
    @5
    uniiun
    @100
    @92
    @114
    @113
    wceq
    @74
    @16
    @87
    @92
    simprrr
    vq
    @5
    @88
    @90
    iuneq2
    syl
    syl5eq
    eqtrd
    @113
    @105
    wss
    @90
    @105
    wss
    #
    vq
    @5
    wral
    @115
    vq
    @5
    @39
    @89
    @105
    @39
    @103
    wcel
    @39
    @105
    wss
    @102
    @103
    @39
    @102
    @101
    ssun2
    vs
    vsnid
    sselii
    @39
    @103
    elssuni
    ax-mp
    @89
    @101
    cuni
    @105
    @86
    @88
    fvssunirn
    @101
    @103
    @101
    @102
    ssun1
    unissi
    sstri
    unssi
    rgenw
    vq
    @5
    @90
    @105
    iunss
    mpbir
    syl6eqss
    @100
    @103
    cJ
    wss
    #
    @105
    cX
    wss
    @100
    @101
    @102
    cJ
    @100
    @101
    @19
    cJ
    @109
    @45
    @32
    @51
    @99
    @62
    ad2antrr
    sstrd
    @100
    @39
    cJ
    @45
    @61
    @51
    @99
    @64
    ad2antrr
    snssd
    unssd
    @116
    @105
    @65
    cX
    @103
    cJ
    uniss
    comppfsc.1
    syl6sseqr
    syl
    eqssd
    @24
    @106
    vb
    @103
    @26
    @22
    @103
    wceq
    @23
    @105
    cX
    @22
    @103
    unieq
    eqeq2d
    rspcev
    syl2anc
    expr
    exlimdv
    ex
    mpdd
    3syld
    ex
    com23
    rexlimdv
    syld
    rexlimdvaa
    syld
    exlimdv
    syl5bi
    pm2.61dne
    syl3an3
    3exp
    com24
    ralrimdv
    @1
    @0
    @29
    va
    vb
    cJ
    cX
    comppfsc.1
    iscmp
    baibr
    sylibd
    impbid2
end
