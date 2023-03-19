include "wa.mm"
include "cin.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wcel.mm"
include "cmpt.mm"
include "cima.mm"
include "wss.mm"
include "wral.mm"
include "cixp.mm"
include "wrex.mm"
include "cfn.mm"
include "wex.mm"
include "inss2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "nfv.mm"
include "nfan.mm"
include "inss1.mm"
include "sseli.mm"
include "ccnp.mm"
include "co.mm"
include "adantlr.mm"
include "wceq.mm"
include "adantr.mm"
include "cuni.mm"
include "simpr.mm"
include "ctopon.mm"
include "ctop.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnpf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "an32s.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "mptexg.mm"
include "syl.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfmpt.mm"
include "nfeq.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "eqeq12d.mm"
include "rspc.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "wb.mm"
include "mptelixpg.mm"
include "mpbid.mm"
include "cnpimaex.mm"
include "sylan2.mm"
include "ex.mm"
include "ralrimi.mm"
include "eleq2.mm"
include "imaeq2.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "ac6sfi.mm"
include "crn.mm"
include "cint.mm"
include "ad2antrr.mm"
include "toponuni.mm"
include "ineq1d.mm"
include "topontop.mm"
include "frn.mm"
include "ad2antrl.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "fofi.mm"
include "rintopn.mm"
include "simpl.mm"
include "ralimi.mm"
include "ad2antll.mm"
include "ralrn.mm"
include "mpbird.mm"
include "elrint.mm"
include "sylanbrc.mm"
include "cdif.mm"
include "wfun.mm"
include "cdm.mm"
include "funmpt.mm"
include "simp-4l.mm"
include "simpllr.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "toponss.mm"
include "sseldi.mm"
include "dmmptg.mm"
include "sseqtr4d.mm"
include "funimass4.mm"
include "sylancr.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "cbvral.mm"
include "syl6bb.mm"
include "ssralv.mm"
include "mpsyl.mm"
include "wi.mm"
include "fnfvelrn.mm"
include "intss1.mm"
include "syl5ss.mm"
include "r19.26.mm"
include "sylan.mm"
include "biimpd.mm"
include "expimpd.mm"
include "ralimia.mm"
include "sylbir.mm"
include "syl6an.mm"
include "sylbid.mm"
include "ralimdaa.mm"
include "impr.mm"
include "eldifi.mm"
include "syl2an.mm"
include "ralbidv.mm"
include "cun.mm"
include "inundif.mm"
include "raleqi.mm"
include "ralunb.mm"
include "bitr3i.mm"
include "ralcom.mm"
include "syl2anr.mm"
include "bitrd.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "ralrimivw.mm"
include "syl5sseqr.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "exlimddv.mm"

theorem ptcnplem
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cD: class D
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let va: setvar a
  let vn: setvar n
  assume ptcnp.2: |- K = ( Xt_ ` F )
  assume ptcnp.3: |- ( ph -> J e. ( TopOn ` X ) )
  assume ptcnp.4: |- ( ph -> I e. V )
  assume ptcnp.5: |- ( ph -> F : I --> Top )
  assume ptcnp.6: |- ( ph -> D e. X )
  assume ptcnp.7: |- ( ( ph /\ k e. I ) -> ( x e. X |-> A ) e. ( ( J CnP ( F ` k ) ) ` D ) )
  assume ptcnplem.1: |- F/ k ps
  assume ptcnplem.2: |- ( ( ph /\ ps ) -> G Fn I )
  assume ptcnplem.3: |- ( ( ( ph /\ ps ) /\ k e. I ) -> ( G ` k ) e. ( F ` k ) )
  assume ptcnplem.4: |- ( ( ph /\ ps ) -> W e. Fin )
  assume ptcnplem.5: |- ( ( ( ph /\ ps ) /\ k e. ( I \ W ) ) -> ( G ` k ) = U. ( F ` k ) )
  assume ptcnplem.6: |- ( ( ph /\ ps ) -> ( ( x e. X |-> ( k e. I |-> A ) ) ` D ) e. X_ k e. I ( G ` k ) )

  disjoint A z
  disjoint k x
  disjoint k z
  disjoint D k
  disjoint x z
  disjoint D x
  disjoint D z
  disjoint I k
  disjoint I x
  disjoint I z
  disjoint G x
  disjoint G z
  disjoint J k
  disjoint J z
  disjoint K z
  disjoint k ph
  disjoint ph x
  disjoint ph z
  disjoint F k
  disjoint F x
  disjoint F z
  disjoint V k
  disjoint V x
  disjoint W k
  disjoint W z
  disjoint X k
  disjoint X x
  disjoint X z
  disjoint f g
  disjoint f t
  disjoint f u
  disjoint f w
  disjoint f z
  disjoint A f
  disjoint g t
  disjoint g u
  disjoint g w
  disjoint g z
  disjoint A g
  disjoint t u
  disjoint t w
  disjoint t z
  disjoint A t
  disjoint u w
  disjoint u z
  disjoint A u
  disjoint w z
  disjoint A w
  disjoint f k
  disjoint f x
  disjoint D f
  disjoint g k
  disjoint g x
  disjoint D g
  disjoint k u
  disjoint k w
  disjoint u x
  disjoint D u
  disjoint w x
  disjoint D w
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint I a
  disjoint f n
  disjoint I f
  disjoint g n
  disjoint I g
  disjoint k n
  disjoint k t
  disjoint n t
  disjoint n w
  disjoint n x
  disjoint n z
  disjoint I n
  disjoint t x
  disjoint I t
  disjoint I w
  disjoint G f
  disjoint G t
  disjoint G u
  disjoint J f
  disjoint J g
  disjoint J u
  disjoint J w
  disjoint K f
  disjoint f ph
  disjoint g ph
  disjoint ph w
  disjoint a u
  disjoint F a
  disjoint F f
  disjoint F g
  disjoint n u
  disjoint F n
  disjoint F u
  disjoint F w
  disjoint f ps
  disjoint V a
  disjoint V g
  disjoint V n
  disjoint V w
  disjoint W f
  disjoint X f
  disjoint X g
  disjoint X t
  disjoint X u
  disjoint X w
  assert |- ( ( ph /\ ps ) -> E. z e. J ( D e. z /\ ( ( x e. X |-> ( k e. I |-> A ) ) " z ) C_ X_ k e. I ( G ` k ) ) )

  proof
    wph
    wps
    wa
    #
    cI
    cW
    cin
    #
    cJ
    vf
    cv
    #
    wf
    #
    cD
    vk
    cv
    #
    @2
    cfv
    #
    wcel
    #
    vx
    cX
    cA
    cmpt
    #
    @5
    cima
    #
    @4
    cG
    cfv
    #
    wss
    #
    wa
    #
    vk
    @1
    wral
    #
    wa
    #
    cD
    vz
    cv
    #
    wcel
    #
    vx
    cX
    vk
    cI
    cA
    cmpt
    #
    cmpt
    #
    @14
    cima
    #
    vk
    cI
    @9
    cixp
    #
    wss
    #
    wa
    #
    vz
    cJ
    wrex
    #
    vf
    @0
    @1
    cfn
    wcel
    #
    cD
    vu
    cv
    #
    wcel
    #
    @7
    @24
    cima
    #
    @9
    wss
    #
    wa
    #
    vu
    cJ
    wrex
    #
    vk
    @1
    wral
    @13
    vf
    wex
    @0
    cW
    cfn
    wcel
    @1
    cW
    wss
    @23
    ptcnplem.4
    cI
    cW
    inss2
    cW
    @1
    ssfi
    sylancl
    #
    @0
    @29
    vk
    @1
    wph
    wps
    vk
    wph
    vk
    nfv
    ptcnplem.1
    nfan
    #
    @0
    @4
    @1
    wcel
    #
    @29
    @32
    @0
    @4
    cI
    wcel
    #
    @29
    @1
    cI
    @4
    cI
    cW
    inss1
    #
    sseli
    @0
    @33
    wa
    @7
    cD
    cJ
    @4
    cF
    cfv
    #
    ccnp
    co
    cfv
    wcel
    #
    @9
    @35
    wcel
    cD
    @7
    cfv
    #
    @9
    wcel
    #
    @29
    wph
    @33
    @36
    wps
    ptcnp.7
    adantlr
    ptcnplem.3
    @0
    @38
    vk
    cI
    @0
    vk
    cI
    @37
    cmpt
    #
    @19
    wcel
    #
    @38
    vk
    cI
    wral
    #
    @0
    @39
    cD
    @17
    cfv
    #
    @19
    @0
    cD
    cX
    wcel
    #
    vk
    cI
    vx
    cv
    #
    @7
    cfv
    #
    cmpt
    #
    @44
    @17
    cfv
    #
    wceq
    #
    vx
    cX
    wral
    #
    @39
    @42
    wceq
    #
    wph
    @43
    wps
    ptcnp.6
    adantr
    wph
    @49
    wps
    wph
    @48
    vx
    cX
    wph
    @44
    cX
    wcel
    #
    wa
    #
    @46
    @16
    @47
    @52
    vk
    cI
    @45
    cA
    wph
    @33
    @51
    @45
    cA
    wceq
    #
    wph
    @33
    wa
    #
    @51
    wa
    @51
    cA
    @35
    cuni
    #
    wcel
    #
    @53
    @54
    @51
    simpr
    @54
    @56
    vx
    cX
    @54
    cX
    @55
    @7
    wf
    #
    @56
    vx
    cX
    wral
    #
    @54
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @35
    @55
    ctopon
    cfv
    wcel
    #
    @36
    @57
    wph
    @59
    @33
    ptcnp.3
    adantr
    @54
    @35
    ctop
    wcel
    @60
    wph
    cI
    ctop
    @4
    cF
    ptcnp.5
    ffvelrnda
    @35
    @55
    @55
    eqid
    toptopon
    sylib
    ptcnp.7
    cD
    @7
    cJ
    @35
    cX
    @55
    cnpf2
    syl3anc
    vx
    cX
    @55
    cA
    @7
    @7
    eqid
    #
    fmpt
    sylibr
    #
    r19.21bi
    #
    vx
    cX
    cA
    @55
    @7
    @61
    fvmpt2
    #
    syl2anc
    an32s
    mpteq2dva
    @52
    @51
    @16
    cvv
    wcel
    #
    @47
    @16
    wceq
    #
    wph
    @51
    simpr
    @52
    cI
    cV
    wcel
    #
    @65
    wph
    @67
    @51
    ptcnp.4
    adantr
    vk
    cI
    cA
    cV
    mptexg
    #
    syl
    vx
    cX
    @16
    cvv
    @17
    @17
    eqid
    fvmpt2
    #
    syl2anc
    eqtr4d
    ralrimiva
    adantr
    @48
    @50
    vx
    cD
    cX
    vx
    @39
    @42
    vx
    vk
    cI
    @37
    vx
    cI
    nfcv
    vx
    cX
    cA
    cD
    nffvmpt1
    nfmpt
    vx
    cX
    @16
    cD
    nffvmpt1
    nfeq
    @44
    cD
    wceq
    #
    @46
    @39
    @47
    @42
    @70
    vk
    cI
    @45
    @37
    @44
    cD
    @7
    fveq2
    mpteq2dv
    @44
    cD
    @17
    fveq2
    eqeq12d
    rspc
    sylc
    ptcnplem.6
    eqeltrd
    @0
    @67
    @40
    @41
    wb
    wph
    @67
    wps
    ptcnp.4
    adantr
    vk
    cI
    @37
    @9
    cV
    mptelixpg
    syl
    mpbid
    r19.21bi
    vu
    @9
    cD
    @7
    cJ
    @35
    cnpimaex
    syl3anc
    sylan2
    ex
    ralrimi
    @28
    @11
    vk
    vu
    @1
    cJ
    vf
    @24
    @5
    wceq
    #
    @25
    @6
    @27
    @10
    @24
    @5
    cD
    eleq2
    @71
    @26
    @8
    @9
    @24
    @5
    @7
    imaeq2
    sseq1d
    anbi12d
    ac6sfi
    syl2anc
    @0
    @13
    wa
    #
    cX
    @2
    crn
    #
    cint
    #
    cin
    #
    cJ
    wcel
    cD
    @75
    wcel
    #
    @17
    @75
    cima
    #
    @19
    wss
    #
    @22
    @72
    @75
    cJ
    cuni
    #
    @74
    cin
    #
    cJ
    @72
    cX
    @79
    @74
    @72
    @59
    cX
    @79
    wceq
    wph
    @59
    wps
    @13
    ptcnp.3
    ad2antrr
    cX
    cJ
    toponuni
    syl
    ineq1d
    @72
    cJ
    ctop
    wcel
    #
    @73
    cJ
    wss
    #
    @73
    cfn
    wcel
    #
    @80
    cJ
    wcel
    wph
    @81
    wps
    @13
    wph
    @59
    @81
    ptcnp.3
    cX
    cJ
    topontop
    syl
    ad2antrr
    @3
    @82
    @0
    @12
    @1
    cJ
    @2
    frn
    ad2antrl
    @72
    @23
    @1
    @73
    @2
    wfo
    #
    @83
    @0
    @23
    @13
    @30
    adantr
    @72
    @2
    @1
    wfn
    #
    @84
    @3
    @85
    @0
    @12
    @1
    cJ
    @2
    ffn
    #
    ad2antrl
    #
    @1
    @2
    dffn4
    sylib
    @1
    @73
    @2
    fofi
    syl2anc
    @73
    cJ
    @79
    @79
    eqid
    rintopn
    syl3anc
    eqeltrd
    @72
    @43
    @15
    vz
    @73
    wral
    #
    @76
    wph
    @43
    wps
    @13
    ptcnp.6
    ad2antrr
    @72
    @88
    @6
    vk
    @1
    wral
    #
    @12
    @89
    @0
    @3
    @11
    @6
    vk
    @1
    @6
    @10
    simpl
    ralimi
    ad2antll
    @72
    @85
    @88
    @89
    wb
    @87
    @15
    @6
    vz
    vk
    @1
    @2
    @14
    @5
    cD
    eleq2
    ralrn
    syl
    mpbird
    vz
    cX
    @73
    cD
    elrint
    sylanbrc
    @72
    @78
    vt
    cv
    #
    @17
    cfv
    #
    @19
    wcel
    #
    vt
    @75
    wral
    #
    @72
    @93
    cA
    @9
    wcel
    #
    vk
    cI
    wral
    #
    vx
    @75
    wral
    #
    @72
    @94
    vx
    @75
    wral
    #
    vk
    cI
    wral
    #
    @96
    @72
    @97
    vk
    @1
    wral
    #
    @97
    vk
    cI
    cW
    cdif
    #
    wral
    #
    @98
    @0
    @3
    @12
    @99
    @0
    @3
    wa
    #
    @11
    @97
    vk
    @1
    @0
    @3
    vk
    @31
    @3
    vk
    nfv
    nfan
    @102
    @32
    wa
    #
    @6
    @10
    @97
    @103
    @6
    wa
    #
    @10
    @45
    @9
    wcel
    #
    vx
    @5
    wral
    #
    @97
    @104
    @10
    @90
    @7
    cfv
    #
    @9
    wcel
    #
    vt
    @5
    wral
    #
    @106
    @104
    @7
    wfun
    @5
    @7
    cdm
    #
    wss
    @10
    @109
    wb
    vx
    cX
    cA
    funmpt
    @104
    @5
    cX
    @110
    @104
    @59
    @5
    cJ
    wcel
    @5
    cX
    wss
    @104
    wph
    @59
    wph
    wps
    @3
    @32
    @6
    simp-4l
    #
    ptcnp.3
    syl
    @104
    @1
    cJ
    @4
    @2
    @0
    @3
    @32
    @6
    simpllr
    #
    @102
    @32
    @6
    simplr
    #
    ffvelrnd
    @5
    cJ
    cX
    toponss
    syl2anc
    @104
    @58
    @110
    cX
    wceq
    @104
    wph
    @33
    @58
    @111
    @104
    @1
    cI
    @4
    @34
    @113
    sseldi
    @62
    syl2anc
    #
    vx
    cX
    cA
    @55
    dmmptg
    syl
    sseqtr4d
    vt
    @5
    @9
    @7
    funimass4
    sylancr
    @108
    @105
    vt
    vx
    @5
    vx
    @107
    @9
    vx
    cX
    cA
    @90
    nffvmpt1
    nfel1
    @105
    vt
    nfv
    @90
    @44
    wceq
    #
    @107
    @45
    @9
    @90
    @44
    @7
    fveq2
    eleq1d
    cbvral
    syl6bb
    @104
    @56
    vx
    @75
    wral
    #
    @106
    @105
    vx
    @75
    wral
    #
    @97
    @75
    cX
    wss
    @104
    @58
    @116
    cX
    @74
    inss1
    #
    @114
    @56
    vx
    @75
    cX
    ssralv
    mpsyl
    @104
    @75
    @5
    wss
    @106
    @117
    wi
    @104
    @75
    @74
    @5
    cX
    @74
    inss2
    @104
    @5
    @73
    wcel
    #
    @74
    @5
    wss
    @104
    @85
    @32
    @119
    @104
    @3
    @85
    @112
    @86
    syl
    @113
    @1
    @4
    @2
    fnfvelrn
    syl2anc
    @5
    @73
    intss1
    syl
    syl5ss
    @105
    vx
    @75
    @5
    ssralv
    syl
    @116
    @117
    wa
    @56
    @105
    wa
    #
    vx
    @75
    wral
    @97
    @56
    @105
    vx
    @75
    r19.26
    @120
    @94
    vx
    @75
    @44
    @75
    wcel
    #
    @56
    @105
    @94
    @121
    @56
    wa
    #
    @105
    @94
    @122
    @45
    cA
    @9
    @121
    @51
    @56
    @53
    @75
    cX
    @44
    @118
    sseli
    #
    @64
    sylan
    eleq1d
    biimpd
    expimpd
    ralimia
    sylbir
    syl6an
    sylbid
    expimpd
    ralimdaa
    impr
    @0
    @101
    @13
    @0
    @97
    vk
    @100
    @31
    @0
    @4
    @100
    wcel
    #
    @97
    @0
    @124
    wa
    #
    @97
    @116
    @0
    wph
    @33
    @116
    @124
    wph
    wps
    simpl
    @4
    cI
    cW
    eldifi
    @54
    @56
    vx
    @75
    @121
    @54
    @51
    @56
    @123
    @63
    sylan2
    ralrimiva
    syl2an
    @125
    @9
    @55
    wceq
    #
    @97
    @116
    wb
    ptcnplem.5
    @126
    @94
    @56
    vx
    @75
    @9
    @55
    cA
    eleq2
    ralbidv
    syl
    mpbird
    ex
    ralrimi
    adantr
    @98
    @97
    vk
    @1
    @100
    cun
    #
    wral
    @99
    @101
    wa
    @97
    vk
    @127
    cI
    cI
    cW
    inundif
    raleqi
    @97
    vk
    @1
    @100
    ralunb
    bitr3i
    sylanbrc
    @94
    vx
    vk
    @75
    cI
    ralcom
    sylibr
    @72
    @67
    @93
    @96
    wb
    wph
    @67
    wps
    @13
    ptcnp.4
    ad2antrr
    @93
    @47
    @19
    wcel
    #
    vx
    @75
    wral
    @67
    @96
    @92
    @128
    vt
    vx
    @75
    vx
    @91
    @19
    vx
    cX
    @16
    @90
    nffvmpt1
    nfel1
    @128
    vt
    nfv
    @115
    @91
    @47
    @19
    @90
    @44
    @17
    fveq2
    eleq1d
    cbvral
    @67
    @128
    @95
    vx
    @75
    @67
    @121
    wa
    #
    @128
    @16
    @19
    wcel
    #
    @95
    @129
    @47
    @16
    @19
    @121
    @51
    @65
    @66
    @67
    @123
    @68
    @69
    syl2anr
    eleq1d
    @67
    @130
    @95
    wb
    @121
    vk
    cI
    cA
    @9
    cV
    mptelixpg
    adantr
    bitrd
    ralbidva
    syl5bb
    syl
    mpbird
    @72
    @17
    wfun
    @75
    @17
    cdm
    #
    wss
    @78
    @93
    wb
    vx
    cX
    @16
    funmpt
    @72
    cX
    @75
    @131
    @118
    @72
    @65
    vx
    cX
    wral
    #
    @131
    cX
    wceq
    wph
    @132
    wps
    @13
    wph
    @65
    vx
    cX
    wph
    @67
    @65
    ptcnp.4
    @68
    syl
    ralrimivw
    ad2antrr
    vx
    cX
    @16
    cvv
    dmmptg
    syl
    syl5sseqr
    vt
    @75
    @19
    @17
    funimass4
    sylancr
    mpbird
    @21
    @76
    @78
    wa
    vz
    @75
    cJ
    @14
    @75
    wceq
    #
    @15
    @76
    @20
    @78
    @14
    @75
    cD
    eleq2
    @133
    @18
    @77
    @19
    @14
    @75
    @17
    imaeq2
    sseq1d
    anbi12d
    rspcev
    syl12anc
    exlimddv
end
