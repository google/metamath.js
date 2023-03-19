include "csn.mm"
include "cv.mm"
include "wf.mm"
include "wa.mm"
include "wral.mm"
include "wex.mm"
include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "cuz.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "w3a.mm"
include "cvv.mm"
include "cxp.mm"
include "cpw.mm"
include "c0.mm"
include "cdif.mm"
include "cfz.mm"
include "wrex.mm"
include "cab.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cmap.mm"
include "wss.mm"
include "simpl.mm"
include "wb.mm"
include "ovex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "syl5ibr.mm"
include "abssdv.mm"
include "ssexg.mm"
include "ralrimivw.mm"
include "abrexex2g.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "uzid.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "simprl.mm"
include "fzsn.mm"
include "feq2d.mm"
include "mpbird.mm"
include "simprr.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "abeq2i.mm"
include "sylibr.mm"
include "cres.mm"
include "wne.mm"
include "wsbc.mm"
include "peano2uzs.mm"
include "ad2antlr.mm"
include "simpr1.mm"
include "simpr3.mm"
include "vex.mm"
include "weq.mm"
include "wi.mm"
include "a1i.mm"
include "sbc2iedv.mm"
include "ad2antrr.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfsbc1v.mm"
include "nfsbc.mm"
include "nfan.mm"
include "sbceq1a.mm"
include "sbcbidv.mm"
include "rspce.mm"
include "eleq2i.mm"
include "nfrex.mm"
include "feq1.mm"
include "rexbidv.mm"
include "elabf.mm"
include "bitri.mm"
include "ex.mm"
include "rexlimdva.mm"
include "elpw2g.mm"
include "cbvrexv.mm"
include "reximdva.mm"
include "rexcom4.mm"
include "syl6ib.mm"
include "syl5bi.mm"
include "ss2abdv.mm"
include "syl5eqss.mm"
include "sselda.mm"
include "eqeq1.mm"
include "3anbi2d.mm"
include "exbidv.mm"
include "elab.mm"
include "sylib.mm"
include "abn0.mm"
include "adantlr.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "adantrl.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "iftrued.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "xpeq1d.mm"
include "biimpar.mm"
include "syldan.mm"
include "0z.mm"
include "elimel.mm"
include "eqid.mm"
include "axdc4uz.mm"
include "syl3anc.mm"
include "abbii.mm"
include "eqtri.mm"
include "feq3.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "eqeq1d.mm"
include "raleqdv.mm"
include "3anbi123d.mm"
include "simpll.mm"
include "sylan.mm"
include "nfre1.mm"
include "nfab.mm"
include "nff.mm"
include "cmpt2.mm"
include "nfcxfr.mm"
include "nfmpt2.mm"
include "nfov.mm"
include "nfel2.mm"
include "nfral.mm"
include "nf3an.mm"
include "simpr2.mm"
include "feq12d.mm"
include "oveq1.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "sdclem2.mm"
include "sylbid.mm"
include "exlimdv.mm"
include "mpd.mm"
include "exlimddv.mm"

theorem sdclem1
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
  let cJ: class J
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vj: setvar j
  let vy: setvar y
  let vm: setvar m
  let cG: class G
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

  disjoint g h
  disjoint g k
  disjoint g ph
  disjoint h k
  disjoint h ph
  disjoint k ph
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
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G w
  disjoint G x
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
    cM
    csn
    #
    cA
    vg
    cv
    #
    wf
    #
    wta
    wa
    #
    cZ
    cA
    vf
    cv
    wf
    wch
    vn
    cZ
    wral
    wa
    vf
    wex
    #
    vg
    sdc.8
    wph
    @3
    wa
    #
    cM
    cz
    wcel
    #
    cM
    cc0
    cif
    #
    cuz
    cfv
    #
    cJ
    vj
    cv
    #
    wf
    #
    @7
    @9
    cfv
    #
    @1
    wceq
    #
    vm
    cv
    #
    c1
    caddc
    co
    #
    @9
    cfv
    #
    @13
    @13
    @9
    cfv
    #
    cF
    co
    #
    wcel
    #
    vm
    @8
    wral
    #
    w3a
    #
    vj
    wex
    #
    @4
    @5
    cJ
    cvv
    wcel
    #
    @1
    cJ
    wcel
    #
    @8
    cJ
    cxp
    #
    cJ
    cpw
    #
    c0
    csn
    cdif
    #
    cF
    wf
    #
    @21
    wph
    @22
    @3
    wph
    cJ
    cM
    vn
    cv
    #
    cfz
    co
    #
    cA
    @1
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
    cvv
    sdc.10
    wph
    cZ
    cvv
    wcel
    @31
    vg
    cab
    #
    cvv
    wcel
    #
    vn
    cZ
    wral
    @33
    cvv
    wcel
    cZ
    cM
    cuz
    cfv
    #
    cvv
    sdc.1
    cM
    cuz
    fvex
    eqeltri
    wph
    @35
    vn
    cZ
    wph
    @34
    cA
    @29
    cmap
    co
    #
    wss
    @37
    cvv
    wcel
    @35
    wph
    @31
    vg
    @37
    @31
    @1
    @37
    wcel
    #
    wph
    @30
    @30
    wps
    simpl
    wph
    cA
    cV
    wcel
    #
    @29
    cvv
    wcel
    @38
    @30
    wb
    sdc.6
    cM
    @28
    cfz
    ovex
    cA
    @29
    @1
    cV
    cvv
    elmapg
    sylancl
    syl5ibr
    abssdv
    cA
    @29
    cmap
    ovex
    @34
    @37
    cvv
    ssexg
    sylancl
    ralrimivw
    @31
    vn
    vg
    cZ
    cvv
    cvv
    abrexex2g
    sylancr
    syl5eqel
    #
    adantr
    @5
    @32
    @23
    @5
    cM
    cZ
    wcel
    cM
    cM
    cfz
    co
    #
    cA
    @1
    wf
    #
    wta
    @32
    @5
    cM
    @36
    cZ
    @5
    @6
    cM
    @36
    wcel
    wph
    @6
    @3
    sdc.7
    adantr
    #
    cM
    uzid
    syl
    sdc.1
    syl6eleqr
    @5
    @42
    @2
    wph
    @2
    wta
    simprl
    #
    @5
    @41
    @0
    cA
    @1
    @5
    @6
    @41
    @0
    wceq
    #
    @43
    cM
    fzsn
    #
    syl
    feq2d
    mpbird
    wph
    @2
    wta
    simprr
    @31
    @42
    wta
    wa
    vn
    cM
    cZ
    @28
    cM
    wceq
    #
    @30
    @42
    wps
    wta
    @47
    @29
    @41
    cA
    @1
    @28
    cM
    cM
    cfz
    oveq2
    feq2d
    sdc.3
    anbi12d
    rspcev
    syl12anc
    @32
    vg
    cJ
    sdc.10
    abeq2i
    sylibr
    wph
    @3
    cZ
    cJ
    cxp
    #
    @26
    cF
    wf
    #
    @27
    @5
    cM
    vk
    cv
    #
    c1
    caddc
    co
    #
    cfz
    co
    #
    cA
    vh
    cv
    #
    wf
    #
    vx
    cv
    #
    @53
    cM
    @50
    cfz
    co
    #
    cres
    #
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
    @26
    wcel
    #
    vx
    cJ
    wral
    vw
    cZ
    wral
    @49
    @5
    @62
    vw
    vx
    cZ
    cJ
    @5
    @55
    cJ
    wcel
    #
    @62
    vw
    cv
    #
    cZ
    wcel
    #
    @5
    @63
    wa
    #
    @61
    @25
    wcel
    #
    @61
    c0
    wne
    #
    @62
    @66
    @67
    @61
    cJ
    wss
    #
    wph
    @69
    @3
    @63
    wph
    @60
    vh
    cJ
    wph
    @59
    @53
    cJ
    wcel
    #
    vk
    cZ
    wph
    @50
    cZ
    wcel
    #
    wa
    #
    @59
    @70
    @72
    @59
    wa
    #
    @29
    cA
    @53
    wf
    #
    wps
    vg
    @53
    wsbc
    #
    wa
    #
    vn
    cZ
    wrex
    #
    @70
    @73
    @51
    cZ
    wcel
    #
    @54
    wps
    vn
    @51
    wsbc
    #
    vg
    @53
    wsbc
    #
    @77
    @71
    @78
    wph
    @59
    cM
    @50
    cZ
    sdc.1
    peano2uzs
    ad2antlr
    @72
    @54
    @58
    wsi
    simpr1
    @73
    @80
    wsi
    @72
    @54
    @58
    wsi
    simpr3
    wph
    @80
    wsi
    wb
    @71
    @59
    wph
    wps
    wsi
    vg
    vn
    @53
    @51
    vh
    vex
    #
    @50
    c1
    caddc
    ovex
    vg
    vh
    weq
    #
    @28
    @51
    wceq
    #
    wa
    wps
    wsi
    wb
    wi
    wph
    sdc.5
    a1i
    sbc2iedv
    ad2antrr
    mpbird
    @76
    @54
    @80
    wa
    vn
    @51
    cZ
    @54
    @80
    vn
    @54
    vn
    nfv
    @79
    vn
    vg
    @53
    vn
    @53
    nfcv
    wps
    vn
    @51
    nfsbc1v
    nfsbc
    nfan
    @83
    @74
    @54
    @75
    @80
    @83
    @29
    @52
    cA
    @53
    @28
    @51
    cM
    cfz
    oveq2
    feq2d
    @83
    wps
    @79
    vg
    @53
    wps
    vn
    @51
    sbceq1a
    sbcbidv
    anbi12d
    rspce
    syl12anc
    @70
    @53
    @33
    wcel
    @77
    cJ
    @33
    @53
    sdc.10
    eleq2i
    @32
    @77
    vg
    @53
    @76
    vg
    vn
    cZ
    vg
    cZ
    nfcv
    @74
    @75
    vg
    @74
    vg
    nfv
    wps
    vg
    @53
    nfsbc1v
    nfan
    nfrex
    @81
    @82
    @31
    @76
    vn
    cZ
    @82
    @30
    @74
    wps
    @75
    @29
    cA
    @1
    @53
    feq1
    wps
    vg
    @53
    sbceq1a
    anbi12d
    rexbidv
    elabf
    bitri
    sylibr
    ex
    rexlimdva
    abssdv
    ad2antrr
    @66
    @22
    @67
    @69
    wb
    wph
    @22
    @3
    @63
    @40
    ad2antrr
    @61
    cJ
    cvv
    elpw2g
    syl
    mpbird
    wph
    @63
    @68
    @3
    wph
    @63
    wa
    #
    @60
    vh
    wex
    #
    @68
    @84
    @55
    @54
    @1
    @57
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
    wex
    #
    vg
    cab
    #
    wcel
    @85
    wph
    cJ
    @90
    @55
    wph
    cJ
    @33
    @90
    sdc.10
    wph
    @32
    @89
    vg
    @32
    @56
    cA
    @1
    wf
    #
    wth
    wa
    #
    vk
    cZ
    wrex
    #
    wph
    @89
    @31
    @92
    vn
    vk
    cZ
    vn
    vk
    weq
    #
    @30
    @91
    wps
    wth
    @94
    @29
    @56
    cA
    @1
    @28
    @50
    cM
    cfz
    oveq2
    feq2d
    sdc.4
    anbi12d
    cbvrexv
    #
    wph
    @93
    @87
    vh
    wex
    #
    vk
    cZ
    wrex
    @89
    wph
    @92
    @96
    vk
    cZ
    sdc.9
    reximdva
    @87
    vk
    vh
    cZ
    rexcom4
    syl6ib
    syl5bi
    ss2abdv
    syl5eqss
    sselda
    @89
    @85
    vg
    @55
    vx
    vex
    vg
    vx
    weq
    #
    @88
    @60
    vh
    @97
    @87
    @59
    vk
    cZ
    @97
    @86
    @58
    @54
    wsi
    @1
    @55
    @57
    eqeq1
    3anbi2d
    rexbidv
    exbidv
    elab
    sylib
    @60
    vh
    abn0
    sylibr
    adantlr
    @61
    @25
    c0
    eldifsn
    sylanbrc
    adantrl
    ralrimivva
    vw
    vx
    cZ
    cJ
    @61
    @26
    cF
    sdc.11
    fmpt2
    sylib
    wph
    @27
    @49
    wph
    @24
    @48
    @26
    cF
    wph
    @8
    cZ
    cJ
    wph
    @8
    @36
    cZ
    wph
    @7
    cM
    cuz
    wph
    @6
    cM
    cc0
    sdc.7
    iftrued
    fveq2d
    sdc.1
    syl6eqr
    xpeq1d
    feq2d
    biimpar
    syldan
    cJ
    @1
    vj
    vm
    cF
    @7
    cvv
    @8
    cM
    cc0
    cz
    0z
    elimel
    @8
    eqid
    axdc4uz
    syl3anc
    @5
    @20
    @4
    vj
    @5
    @20
    cZ
    @93
    vg
    cab
    #
    @9
    wf
    #
    cM
    @9
    cfv
    #
    @1
    wceq
    #
    @18
    vm
    cZ
    wral
    #
    w3a
    #
    @4
    @5
    @10
    @99
    @12
    @101
    @19
    @102
    @5
    @10
    cZ
    cJ
    @9
    wf
    #
    @99
    @5
    @8
    cZ
    cJ
    @9
    @5
    @8
    @36
    cZ
    @5
    @7
    cM
    cuz
    @5
    @6
    cM
    cc0
    @43
    iftrued
    #
    fveq2d
    sdc.1
    syl6eqr
    #
    feq2d
    cJ
    @98
    wceq
    @104
    @99
    wb
    cJ
    @33
    @98
    sdc.10
    @32
    @93
    vg
    @95
    abbii
    eqtri
    #
    cJ
    @98
    cZ
    @9
    feq3
    ax-mp
    #
    syl6bb
    @5
    @11
    @100
    @1
    @5
    @7
    cM
    @9
    @105
    fveq2d
    eqeq1d
    @5
    @18
    vm
    @8
    cZ
    @106
    raleqdv
    3anbi123d
    @5
    @103
    @4
    @5
    @103
    wa
    #
    wps
    wch
    wth
    wta
    wsi
    vx
    vw
    cA
    vf
    vg
    vh
    vk
    vn
    cF
    @9
    cJ
    cM
    cV
    cZ
    sdc.1
    sdc.2
    sdc.3
    sdc.4
    sdc.5
    wph
    @39
    @3
    @103
    sdc.6
    ad2antrr
    wph
    @6
    @3
    @103
    sdc.7
    ad2antrr
    #
    wph
    @3
    vg
    wex
    @3
    @103
    sdc.8
    ad2antrr
    @109
    wph
    @71
    @92
    @96
    wi
    wph
    @3
    @103
    simpll
    sdc.9
    sylan
    sdc.10
    sdc.11
    @5
    @103
    vk
    @5
    vk
    nfv
    @99
    @101
    @102
    vk
    vk
    cZ
    @98
    @9
    vk
    @9
    nfcv
    vk
    cZ
    nfcv
    #
    @93
    vk
    vg
    @92
    vk
    cZ
    nfre1
    nfab
    #
    nff
    @101
    vk
    nfv
    @18
    vk
    vm
    cZ
    @111
    vk
    @15
    @17
    vk
    @13
    @16
    cF
    vk
    @13
    nfcv
    vk
    cF
    vw
    vx
    cZ
    cJ
    @61
    cmpt2
    sdc.11
    vw
    vx
    vk
    cZ
    cJ
    @61
    @111
    vk
    cJ
    @98
    @107
    @112
    nfcxfr
    @60
    vk
    vh
    @59
    vk
    cZ
    nfre1
    nfab
    nfmpt2
    nfcxfr
    vk
    @16
    nfcv
    nfov
    nfel2
    nfral
    nf3an
    nfan
    @109
    @99
    @104
    @5
    @99
    @101
    @102
    simpr1
    @108
    sylibr
    @109
    @41
    cA
    @100
    wf
    @2
    @5
    @2
    @103
    @44
    adantr
    @109
    @41
    @0
    cA
    @100
    @1
    @5
    @99
    @101
    @102
    simpr2
    @109
    @6
    @45
    @110
    @46
    syl
    feq12d
    mpbird
    @109
    @102
    @65
    @64
    c1
    caddc
    co
    #
    @9
    cfv
    #
    @64
    @64
    @9
    cfv
    #
    cF
    co
    #
    wcel
    #
    @5
    @99
    @101
    @102
    simpr3
    @18
    @117
    vm
    @64
    cZ
    vm
    vw
    weq
    #
    @15
    @114
    @17
    @116
    @118
    @14
    @113
    @9
    @13
    @64
    c1
    caddc
    oveq1
    fveq2d
    @118
    @13
    @64
    @16
    @115
    cF
    @118
    id
    @13
    @64
    @9
    fveq2
    oveq12d
    eleq12d
    rspccva
    sylan
    sdclem2
    ex
    sylbid
    exlimdv
    mpd
    exlimddv
end
