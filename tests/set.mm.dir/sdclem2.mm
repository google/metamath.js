include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wf.mm"
include "cfz.mm"
include "co.mm"
include "wsbc.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "wcel.mm"
include "wrex.mm"
include "ffvelrnda.mm"
include "cab.mm"
include "eleq2i.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfan.mm"
include "nfrex.mm"
include "fvex.mm"
include "wceq.mm"
include "feq1.mm"
include "sbceq1a.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "elabf.mm"
include "bitri.mm"
include "sylib.mm"
include "weq.mm"
include "cdm.mm"
include "fdm.mm"
include "adantr.mm"
include "wi.mm"
include "cuz.mm"
include "c1.mm"
include "caddc.mm"
include "fveq2.mm"
include "oveq2.mm"
include "mpteq1d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "cz.mm"
include "id.mm"
include "fveq12d.mm"
include "eqid.mm"
include "fvmpt.mm"
include "adantl.mm"
include "elfz1eq.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqtr2d.mm"
include "ex.mm"
include "ralrimi.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "syl.mm"
include "fnmpti.mm"
include "eqfnfv.mm"
include "sylancl.mm"
include "mpbird.mm"
include "a1i.mm"
include "cres.mm"
include "w3a.mm"
include "cvv.mm"
include "simpr.mm"
include "wss.mm"
include "3simpa.mm"
include "reximi.mm"
include "ss2abi.mm"
include "eqeltri.mm"
include "cmap.mm"
include "simpl.mm"
include "ovex.mm"
include "elmapg.mm"
include "mpan2.mm"
include "syl5ibr.mm"
include "abssdv.mm"
include "ssexg.mm"
include "a1d.mm"
include "abrexex2g.mm"
include "sylancr.mm"
include "eqeq1.mm"
include "3anbi2d.mm"
include "abbidv.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "ovmpt4g.mm"
include "3com12.mm"
include "3exp.mm"
include "vtoclga.mm"
include "syl3c.mm"
include "syl6eqss.mm"
include "sseldd.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "elab.mm"
include "simprl.mm"
include "fzssp1.mm"
include "fssres.mm"
include "simprr.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "fndm.mm"
include "eqtr3d.mm"
include "simplr.mm"
include "syl6eleq.mm"
include "fzopth.mm"
include "mpbid.mm"
include "simprd.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "wo.mm"
include "elfzp1.mm"
include "reseq2d.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "fvres.mm"
include "syl5ibcom.mm"
include "eqeltrrd.mm"
include "peano2uz.mm"
include "eluzfz2.mm"
include "4syl.mm"
include "eqcomd.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "jaod.mm"
include "ralrimiv.mm"
include "ad2antrl.mm"
include "eqfnfv2.mm"
include "mpbir2and.mm"
include "expr.mm"
include "imbi1d.mm"
include "expimpd.mm"
include "rexlimd.mm"
include "mpd.mm"
include "expcom.mm"
include "sylbir.mm"
include "a2d.mm"
include "uzind4.mm"
include "eleq2s.mm"
include "impcom.mm"
include "dmeqd.mm"
include "dmmptg.mm"
include "mprg.mm"
include "syl6eq.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "syl6bi.mm"
include "syl5.mm"
include "feq2d.mm"
include "sbcbidv.mm"
include "equcoms.mm"
include "biimpcd.mm"
include "sylcom.mm"
include "rexlimdvw.mm"
include "simpld.mm"
include "ffvelrnd.mm"
include "cbvmptv.mm"
include "fmptdf.mm"
include "sbceq1dd.mm"
include "mpteq1.mm"
include "dfsbcq.mm"
include "3syl.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "mptex.mm"
include "vex.mm"
include "resex.mm"
include "sbcie.mm"
include "fzssuz.mm"
include "sseqtr4i.mm"
include "sbceq1d.mm"
include "syl5bbr.mm"
include "ralbidv.mm"
include "spcev.mm"
include "syl2anc.mm"

theorem sdclem2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wsi: wff si
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cJ: class J
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vj: setvar j
  let vy: setvar y
  let vm: setvar m
  assume sdc.1: |- Z = ( ZZ>= ` M )
  assume sdc.2: |- ( g = ( f |` ( M ... n ) ) -> ( ps <-> ch ) )
  assume sdc.3: |- ( n = M -> ( ps <-> ta ) )
  assume sdc.4: |- ( n = k -> ( ps <-> th ) )
  assume sdc.5: |- ( ( g = h /\ n = ( k + 1 ) ) -> ( ps <-> si ) )
  assume sdc.6: |- ( ph -> A e. V )
  assume sdc.7: |- ( ph -> M e. ZZ )
  assume sdc.8: |- ( ph -> E. g ( g : { M } --> A /\ ta ) )
  assume sdc.9: |- ( ( ph /\ k e. Z ) -> ( ( g : ( M ... k ) --> A /\ th ) -> E. h ( h : ( M ... ( k + 1 ) ) --> A /\ g = ( h |` ( M ... k ) ) /\ si ) ) )
  assume sdc.10: |- J = { g | E. n e. Z ( g : ( M ... n ) --> A /\ ps ) }
  assume sdc.11: |- F = ( w e. Z , x e. J |-> { h | E. k e. Z ( h : ( M ... ( k + 1 ) ) --> A /\ x = ( h |` ( M ... k ) ) /\ si ) } )
  assume sdc.12: |- F/ k ph
  assume sdc.13: |- ( ph -> G : Z --> J )
  assume sdc.14: |- ( ph -> ( G ` M ) : ( M ... M ) --> A )
  assume sdc.15: |- ( ( ph /\ w e. Z ) -> ( G ` ( w + 1 ) ) e. ( w F ( G ` w ) ) )

  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint A f
  disjoint g h
  disjoint g k
  disjoint g n
  disjoint g w
  disjoint g x
  disjoint A g
  disjoint h k
  disjoint h n
  disjoint h w
  disjoint h x
  disjoint A h
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint A k
  disjoint n w
  disjoint n x
  disjoint A n
  disjoint w x
  disjoint A w
  disjoint A x
  disjoint J h
  disjoint J k
  disjoint J w
  disjoint J x
  disjoint M f
  disjoint M g
  disjoint M h
  disjoint M k
  disjoint M n
  disjoint M w
  disjoint M x
  disjoint ch g
  disjoint F n
  disjoint F w
  disjoint F x
  disjoint f ps
  disjoint h ps
  disjoint k ps
  disjoint ps x
  disjoint f si
  disjoint g si
  disjoint n si
  disjoint si x
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G k
  disjoint G n
  disjoint G w
  disjoint G x
  disjoint n ph
  disjoint ph w
  disjoint ph x
  disjoint n th
  disjoint th w
  disjoint th x
  disjoint V h
  disjoint h ta
  disjoint k ta
  disjoint n ta
  disjoint ta w
  disjoint ta x
  disjoint Z f
  disjoint Z g
  disjoint Z h
  disjoint Z k
  disjoint Z n
  disjoint Z w
  disjoint Z x
  disjoint f j
  disjoint f y
  disjoint g j
  disjoint g y
  disjoint h j
  disjoint h y
  disjoint j k
  disjoint j n
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint k y
  disjoint n y
  disjoint w y
  disjoint x y
  disjoint A y
  disjoint h m
  disjoint j m
  disjoint J j
  disjoint k m
  disjoint m w
  disjoint m x
  disjoint J m
  disjoint f m
  disjoint g m
  disjoint M j
  disjoint m n
  disjoint m y
  disjoint M m
  disjoint M y
  disjoint ch j
  disjoint F j
  disjoint F m
  disjoint j ps
  disjoint ps y
  disjoint j si
  disjoint si y
  disjoint G j
  disjoint G m
  disjoint j ph
  disjoint ph y
  disjoint th y
  disjoint j ta
  disjoint ta y
  disjoint Z j
  disjoint Z m
  disjoint Z y
  assert |- ( ph -> E. f ( f : Z --> A /\ A. n e. Z ch ) )

  proof
    wph
    cZ
    cA
    vm
    cZ
    vm
    cv
    #
    @0
    cG
    cfv
    #
    cfv
    #
    cmpt
    #
    wf
    #
    wps
    vg
    vm
    cM
    vn
    cv
    #
    cfz
    co
    #
    @2
    cmpt
    #
    wsbc
    #
    vn
    cZ
    wral
    #
    cZ
    cA
    vf
    cv
    #
    wf
    #
    wch
    vn
    cZ
    wral
    #
    wa
    #
    vf
    wex
    wph
    vk
    cZ
    vk
    cv
    #
    @14
    cG
    cfv
    #
    cfv
    #
    cA
    @3
    sdc.12
    wph
    @14
    cZ
    wcel
    #
    wa
    #
    cM
    @14
    cfz
    co
    #
    cA
    @14
    @15
    @18
    @19
    cA
    @15
    wf
    #
    wth
    vg
    @15
    wsbc
    #
    @18
    @6
    cA
    @15
    wf
    #
    wps
    vg
    @15
    wsbc
    #
    wa
    #
    vn
    cZ
    wrex
    #
    @20
    @21
    wa
    #
    @18
    @15
    cJ
    wcel
    #
    @25
    wph
    cZ
    cJ
    @14
    cG
    sdc.13
    ffvelrnda
    @27
    @15
    @6
    cA
    vg
    cv
    #
    wf
    #
    wps
    wa
    #
    vn
    cZ
    wrex
    #
    vg
    cab
    #
    wcel
    @25
    cJ
    @32
    @15
    sdc.10
    eleq2i
    @31
    @25
    vg
    @15
    @24
    vg
    vn
    cZ
    vg
    cZ
    nfcv
    @22
    @23
    vg
    @22
    vg
    nfv
    wps
    vg
    @15
    nfsbc1v
    nfan
    nfrex
    @14
    cG
    fvex
    @28
    @15
    wceq
    #
    @30
    @24
    vn
    cZ
    @33
    @29
    @22
    wps
    @23
    @6
    cA
    @28
    @15
    feq1
    wps
    vg
    @15
    sbceq1a
    anbi12d
    rexbidv
    elabf
    bitri
    sylib
    @18
    @24
    @26
    vn
    cZ
    @18
    @24
    vk
    vn
    weq
    #
    @26
    @24
    @15
    cdm
    #
    @6
    wceq
    #
    @18
    @34
    @22
    @36
    @23
    @6
    cA
    @15
    fdm
    adantr
    @18
    @36
    cM
    cM
    wceq
    #
    @34
    wa
    #
    @34
    @18
    @36
    @19
    @6
    wceq
    #
    @38
    @18
    @35
    @19
    @6
    @18
    @35
    vm
    @19
    @2
    cmpt
    #
    cdm
    #
    @19
    @18
    @15
    @40
    @17
    wph
    @15
    @40
    wceq
    #
    wph
    @42
    wi
    #
    @14
    cM
    cuz
    cfv
    #
    cZ
    wph
    vx
    cv
    #
    cG
    cfv
    #
    vm
    cM
    @45
    cfz
    co
    #
    @2
    cmpt
    #
    wceq
    #
    wi
    wph
    cM
    cG
    cfv
    #
    vm
    cM
    cM
    cfz
    co
    #
    @2
    cmpt
    #
    wceq
    #
    wi
    #
    wph
    vw
    cv
    #
    cG
    cfv
    #
    vm
    cM
    @55
    cfz
    co
    #
    @2
    cmpt
    #
    wceq
    #
    wi
    wph
    @55
    c1
    caddc
    co
    #
    cG
    cfv
    #
    vm
    cM
    @60
    cfz
    co
    #
    @2
    cmpt
    #
    wceq
    #
    wi
    @43
    vx
    vw
    cM
    @14
    @45
    cM
    wceq
    #
    @49
    @53
    wph
    @65
    @46
    @50
    @48
    @52
    @45
    cM
    cG
    fveq2
    @65
    vm
    @47
    @51
    @2
    @45
    cM
    cM
    cfz
    oveq2
    mpteq1d
    eqeq12d
    imbi2d
    vx
    vw
    weq
    #
    @49
    @59
    wph
    @66
    @46
    @56
    @48
    @58
    @45
    @55
    cG
    fveq2
    @66
    vm
    @47
    @57
    @2
    @45
    @55
    cM
    cfz
    oveq2
    mpteq1d
    eqeq12d
    imbi2d
    @45
    @60
    wceq
    #
    @49
    @64
    wph
    @67
    @46
    @61
    @48
    @63
    @45
    @60
    cG
    fveq2
    @67
    vm
    @47
    @62
    @2
    @45
    @60
    cM
    cfz
    oveq2
    mpteq1d
    eqeq12d
    imbi2d
    vx
    vk
    weq
    #
    @49
    @42
    wph
    @68
    @46
    @15
    @48
    @40
    @45
    @14
    cG
    fveq2
    @68
    vm
    @47
    @19
    @2
    @45
    @14
    cM
    cfz
    oveq2
    mpteq1d
    eqeq12d
    imbi2d
    @54
    cM
    cz
    wcel
    wph
    @53
    @14
    @50
    cfv
    #
    @14
    @52
    cfv
    #
    wceq
    #
    vk
    @51
    wral
    #
    wph
    @71
    vk
    @51
    sdc.12
    wph
    @14
    @51
    wcel
    #
    @71
    wph
    @73
    wa
    #
    @70
    @16
    @69
    @73
    @70
    @16
    wceq
    wph
    vm
    @14
    @2
    @16
    @51
    @52
    vm
    vk
    weq
    #
    @0
    @14
    @1
    @15
    @0
    @14
    cG
    fveq2
    @75
    id
    fveq12d
    #
    @52
    eqid
    #
    @14
    @15
    fvex
    fvmpt
    adantl
    @74
    @14
    @15
    @50
    @74
    @14
    cM
    cG
    @73
    @14
    cM
    wceq
    wph
    @14
    cM
    elfz1eq
    adantl
    fveq2d
    fveq1d
    eqtr2d
    ex
    ralrimi
    wph
    @50
    @51
    wfn
    #
    @52
    @51
    wfn
    @53
    @72
    wb
    wph
    @51
    cA
    @50
    wf
    @78
    sdc.14
    @51
    cA
    @50
    ffn
    syl
    vm
    @51
    @2
    @52
    @0
    @1
    fvex
    #
    @77
    fnmpti
    vk
    @51
    @50
    @52
    eqfnfv
    sylancl
    mpbird
    a1i
    @55
    @44
    wcel
    #
    wph
    @59
    @64
    @80
    @55
    cZ
    wcel
    #
    wph
    @59
    @64
    wi
    #
    wi
    cZ
    @44
    @55
    sdc.1
    eleq2i
    wph
    @81
    @82
    wph
    @81
    wa
    #
    cM
    @14
    c1
    caddc
    co
    #
    cfz
    co
    #
    cA
    @61
    wf
    #
    @56
    @61
    @19
    cres
    #
    wceq
    #
    wa
    #
    vk
    cZ
    wrex
    #
    @82
    @83
    @61
    @85
    cA
    vh
    cv
    #
    wf
    #
    @56
    @91
    @19
    cres
    #
    wceq
    #
    wa
    #
    vk
    cZ
    wrex
    #
    vh
    cab
    #
    wcel
    @90
    @83
    @55
    @56
    cF
    co
    #
    @97
    @61
    @83
    @98
    @92
    @94
    wsi
    w3a
    #
    vk
    cZ
    wrex
    #
    vh
    cab
    #
    @97
    @83
    @56
    cJ
    wcel
    @81
    @101
    cvv
    wcel
    #
    @98
    @101
    wceq
    #
    wph
    cZ
    cJ
    @55
    cG
    sdc.13
    ffvelrnda
    wph
    @81
    simpr
    @83
    @101
    @97
    wss
    @97
    cvv
    wcel
    #
    @102
    @100
    @96
    vh
    @99
    @95
    vk
    cZ
    @92
    @94
    wsi
    3simpa
    reximi
    ss2abi
    #
    @83
    cZ
    cvv
    wcel
    @95
    vh
    cab
    #
    cvv
    wcel
    #
    vk
    cZ
    wral
    @104
    cZ
    @44
    cvv
    sdc.1
    cM
    cuz
    fvex
    eqeltri
    #
    @83
    @107
    vk
    cZ
    wph
    @81
    vk
    sdc.12
    @81
    vk
    nfv
    nfan
    #
    @83
    @107
    @17
    @83
    @106
    cA
    @85
    cmap
    co
    #
    wss
    #
    @110
    cvv
    wcel
    @107
    @83
    cA
    cV
    wcel
    #
    @111
    wph
    @112
    @81
    sdc.6
    adantr
    @112
    @95
    vh
    @110
    @95
    @91
    @110
    wcel
    #
    @112
    @92
    @92
    @94
    simpl
    @112
    @85
    cvv
    wcel
    @113
    @92
    wb
    cM
    @84
    cfz
    ovex
    cA
    @85
    @91
    cV
    cvv
    elmapg
    mpan2
    syl5ibr
    abssdv
    syl
    cA
    @85
    cmap
    ovex
    @106
    @110
    cvv
    ssexg
    sylancl
    a1d
    ralrimi
    @95
    vk
    vh
    cZ
    cvv
    cvv
    abrexex2g
    sylancr
    @101
    @97
    cvv
    ssexg
    sylancr
    @81
    @92
    @45
    @93
    wceq
    #
    wsi
    w3a
    #
    vk
    cZ
    wrex
    #
    vh
    cab
    #
    cvv
    wcel
    #
    @55
    @45
    cF
    co
    #
    @117
    wceq
    #
    wi
    #
    wi
    @81
    @102
    @103
    wi
    #
    wi
    vx
    @56
    cJ
    @45
    @56
    wceq
    #
    @121
    @122
    @81
    @123
    @118
    @102
    @120
    @103
    @123
    @117
    @101
    cvv
    @123
    @116
    @100
    vh
    @123
    @115
    @99
    vk
    cZ
    @123
    @114
    @94
    @92
    wsi
    @45
    @56
    @93
    eqeq1
    3anbi2d
    rexbidv
    abbidv
    #
    eleq1d
    @123
    @119
    @98
    @117
    @101
    @45
    @56
    @55
    cF
    oveq2
    @124
    eqeq12d
    imbi12d
    imbi2d
    @45
    cJ
    wcel
    #
    @81
    @118
    @120
    @81
    @125
    @118
    @120
    vw
    vx
    cZ
    cJ
    @117
    cF
    cvv
    sdc.11
    ovmpt4g
    3com12
    3exp
    vtoclga
    syl3c
    @105
    syl6eqss
    sdc.15
    sseldd
    @96
    @90
    vh
    @61
    @60
    cG
    fvex
    @91
    @61
    wceq
    #
    @95
    @89
    vk
    cZ
    @126
    @92
    @86
    @94
    @88
    @85
    cA
    @91
    @61
    feq1
    @126
    @93
    @87
    @56
    @91
    @61
    @19
    reseq1
    eqeq2d
    anbi12d
    rexbidv
    elab
    sylib
    @83
    @89
    @82
    vk
    cZ
    @109
    @82
    vk
    nfv
    @83
    @17
    @89
    @82
    wi
    @83
    @17
    wa
    #
    @86
    @88
    @82
    @127
    @86
    wa
    @82
    @88
    @87
    @58
    wceq
    #
    @64
    wi
    @127
    @86
    @128
    @64
    @127
    @86
    @128
    wa
    #
    wa
    #
    @64
    @85
    @62
    wceq
    #
    @45
    @61
    cfv
    #
    @45
    @63
    cfv
    #
    wceq
    #
    vx
    @85
    wral
    #
    @130
    @84
    @60
    cM
    cfz
    @130
    @14
    @55
    c1
    caddc
    @130
    @37
    vk
    vw
    weq
    #
    @130
    @19
    @57
    wceq
    #
    @37
    @136
    wa
    #
    @130
    @87
    cdm
    #
    @19
    @57
    @130
    @19
    cA
    @87
    wf
    #
    @139
    @19
    wceq
    @130
    @86
    @19
    @85
    wss
    @140
    @127
    @86
    @128
    simprl
    cM
    @14
    fzssp1
    @85
    cA
    @19
    @61
    fssres
    sylancl
    @19
    cA
    @87
    fdm
    syl
    @130
    @87
    @57
    wfn
    #
    @139
    @57
    wceq
    @130
    @141
    @58
    @57
    wfn
    vm
    @57
    @2
    @58
    @79
    @58
    eqid
    fnmpti
    @130
    @57
    @87
    @58
    @127
    @86
    @128
    simprr
    #
    fneq1d
    mpbiri
    @57
    @87
    fndm
    syl
    eqtr3d
    #
    @130
    @14
    @44
    wcel
    #
    @137
    @138
    wb
    @130
    @14
    cZ
    @44
    @83
    @17
    @129
    simplr
    sdc.1
    syl6eleq
    #
    cM
    @55
    cM
    @14
    fzopth
    syl
    mpbid
    simprd
    #
    oveq1d
    #
    oveq2d
    @130
    @134
    vx
    @85
    @130
    @45
    @85
    wcel
    #
    @45
    @19
    wcel
    #
    @45
    @84
    wceq
    #
    wo
    #
    @134
    @130
    @144
    @148
    @151
    wb
    @145
    @45
    cM
    @14
    elfzp1
    syl
    @130
    @149
    @134
    @150
    @130
    @45
    @87
    cfv
    #
    @45
    @63
    @19
    cres
    #
    cfv
    #
    wceq
    @149
    @134
    @130
    @45
    @87
    @153
    @130
    @87
    @58
    @153
    @142
    @130
    @153
    @63
    @57
    cres
    #
    @58
    @130
    @19
    @57
    @63
    @143
    reseq2d
    @57
    @62
    wss
    @155
    @58
    wceq
    cM
    @55
    fzssp1
    vm
    @62
    @57
    @2
    resmpt
    ax-mp
    syl6req
    eqtrd
    fveq1d
    @149
    @152
    @132
    @154
    @133
    @45
    @19
    @61
    fvres
    @45
    @19
    @63
    fvres
    eqeq12d
    syl5ibcom
    @130
    @150
    @67
    @134
    @130
    @84
    @60
    @45
    @147
    eqeq2d
    @130
    @134
    @67
    @60
    @61
    cfv
    #
    @60
    @63
    cfv
    #
    wceq
    @130
    @157
    @156
    @130
    @80
    @60
    @44
    wcel
    @60
    @62
    wcel
    @157
    @156
    wceq
    @130
    @14
    @55
    @44
    @146
    @145
    eqeltrrd
    cM
    @55
    peano2uz
    cM
    @60
    eluzfz2
    vm
    @60
    @2
    @156
    @62
    @63
    @0
    @60
    wceq
    #
    @0
    @60
    @1
    @61
    @0
    @60
    cG
    fveq2
    @158
    id
    fveq12d
    @63
    eqid
    #
    @60
    @61
    fvex
    fvmpt
    4syl
    eqcomd
    @67
    @132
    @156
    @133
    @157
    @45
    @60
    @61
    fveq2
    @45
    @60
    @63
    fveq2
    eqeq12d
    syl5ibrcom
    sylbid
    jaod
    sylbid
    ralrimiv
    @130
    @61
    @85
    wfn
    #
    @63
    @62
    wfn
    @64
    @131
    @135
    wa
    wb
    @86
    @160
    @127
    @128
    @85
    cA
    @61
    ffn
    ad2antrl
    vm
    @62
    @2
    @63
    @79
    @159
    fnmpti
    vx
    @85
    @62
    @61
    @63
    eqfnfv2
    sylancl
    mpbir2and
    expr
    @88
    @59
    @128
    @64
    @56
    @87
    @58
    eqeq1
    imbi1d
    syl5ibrcom
    expimpd
    ex
    rexlimd
    mpd
    expcom
    sylbir
    a2d
    uzind4
    sdc.1
    eleq2s
    impcom
    #
    dmeqd
    @2
    cvv
    wcel
    #
    @41
    @19
    wceq
    vm
    @19
    vm
    @19
    @2
    cvv
    dmmptg
    @162
    @0
    @19
    wcel
    @79
    a1i
    mprg
    syl6eq
    eqeq1d
    @18
    @144
    @39
    @38
    wb
    @18
    @14
    cZ
    @44
    wph
    @17
    simpr
    sdc.1
    syl6eleq
    #
    cM
    @5
    cM
    @14
    fzopth
    syl
    bitrd
    @37
    @34
    simpr
    syl6bi
    syl5
    @34
    @24
    @26
    @24
    @26
    wb
    vn
    vk
    vn
    vk
    weq
    #
    @22
    @20
    @23
    @21
    @164
    @6
    @19
    cA
    @15
    @5
    @14
    cM
    cfz
    oveq2
    #
    feq2d
    @164
    wps
    wth
    vg
    @15
    sdc.4
    sbcbidv
    anbi12d
    equcoms
    biimpcd
    sylcom
    rexlimdvw
    mpd
    #
    simpld
    @18
    @144
    @14
    @19
    wcel
    @163
    cM
    @14
    eluzfz2
    syl
    ffvelrnd
    vm
    vk
    cZ
    @2
    @16
    @76
    cbvmptv
    fmptdf
    wph
    wth
    vg
    @40
    wsbc
    #
    vk
    cZ
    wral
    @9
    wph
    @167
    vk
    cZ
    sdc.12
    wph
    @17
    @167
    @18
    wth
    vg
    @15
    @40
    @161
    @18
    @20
    @21
    @166
    simprd
    sbceq1dd
    ex
    ralrimi
    @8
    @167
    vn
    vk
    cZ
    @164
    @8
    wps
    vg
    @40
    wsbc
    #
    @167
    @164
    @6
    @19
    wceq
    @7
    @40
    wceq
    @8
    @168
    wb
    @165
    vm
    @6
    @19
    @2
    mpteq1
    wps
    vg
    @7
    @40
    dfsbcq
    3syl
    @164
    wps
    wth
    vg
    @40
    sdc.4
    sbcbidv
    bitrd
    cbvralv
    sylibr
    @13
    @4
    @9
    wa
    vf
    @3
    vm
    cZ
    @2
    @108
    mptex
    @10
    @3
    wceq
    #
    @11
    @4
    @12
    @9
    cZ
    cA
    @10
    @3
    feq1
    @169
    wch
    @8
    vn
    cZ
    wch
    wps
    vg
    @10
    @6
    cres
    #
    wsbc
    @169
    @8
    wps
    wch
    vg
    @170
    @10
    @6
    vf
    vex
    resex
    sdc.2
    sbcie
    @169
    wps
    vg
    @170
    @7
    @169
    @170
    @3
    @6
    cres
    #
    @7
    @10
    @3
    @6
    reseq1
    @6
    cZ
    wss
    @171
    @7
    wceq
    @6
    @44
    cZ
    cM
    @5
    fzssuz
    sdc.1
    sseqtr4i
    vm
    cZ
    @6
    @2
    resmpt
    ax-mp
    syl6eq
    sbceq1d
    syl5bbr
    ralbidv
    anbi12d
    spcev
    syl2anc
end
