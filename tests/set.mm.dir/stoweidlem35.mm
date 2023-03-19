include "cv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cc0.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "crn.mm"
include "wfn.mm"
include "wf1o.mm"
include "w3a.mm"
include "cfn.mm"
include "crab.mm"
include "wceq.mm"
include "rnmptfi.mm"
include "syl.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "fnchoice.mm"
include "adantl.mm"
include "simprl.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nfrn.mm"
include "nfcri.mm"
include "nfan.mm"
include "sselda.mm"
include "syl6eleq.mm"
include "rabid.mm"
include "sylib.mm"
include "simprd.mm"
include "df-rex.mm"
include "exbii.mm"
include "sylibr.mm"
include "adantr.mm"
include "nfv.mm"
include "nfrab1.mm"
include "nfeq2.mm"
include "eleq2.mm"
include "biimprd.mm"
include "eximd.mm"
include "mpd.mm"
include "adantllr.mm"
include "elrnmpt.mm"
include "ibi.mm"
include "r19.29af.mm"
include "n0.mm"
include "adantlr.mm"
include "simplrr.mm"
include "neeq1.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "imbi12d.mm"
include "rspccva.mm"
include "sylancom.mm"
include "ralrimiva.mm"
include "cbvralv.mm"
include "jca.mm"
include "ex.mm"
include "eximdv.mm"
include "mpdan.mm"
include "ralrimivw.mm"
include "chash.mm"
include "wn.mm"
include "cuni.mm"
include "wss.mm"
include "ssn0.mm"
include "syl2anc.mm"
include "neneqd.mm"
include "unieq.mm"
include "uni0.mm"
include "syl6eq.mm"
include "nsyl.mm"
include "cdm.mm"
include "dm0rn0.mm"
include "cvv.mm"
include "cle.mm"
include "rabexd.mm"
include "rabexgf.mm"
include "fmptdf.mm"
include "dffn2.mm"
include "fndm.mm"
include "eqeq1d.mm"
include "syl5bbr.mm"
include "mtbird.mm"
include "wo.mm"
include "fz1f1o.mm"
include "ord.mm"
include "wb.mm"
include "oveq2.mm"
include "f1oeq2.mm"
include "exbidv.mm"
include "rspcev.mm"
include "r19.29.mm"
include "eeanv.mm"
include "biimpri.mm"
include "a1i.mm"
include "reximdv.mm"
include "wal.mm"
include "ax-5.mm"
include "19.29.mm"
include "sylan.mm"
include "eximi.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "2exbii.mm"
include "simprr1.mm"
include "elex.mm"
include "simprr2.mm"
include "simprr3.mm"
include "nfcv.mm"
include "nfra1.mm"
include "nfrab.mm"
include "nfmpt.mm"
include "nffn.mm"
include "nfral.mm"
include "nff1o.mm"
include "nf3an.mm"
include "stoweidlem27.mm"
include "2eximdv.mm"
include "id.mm"
include "exlimivv.mm"

theorem stoweidlem35
  let wph: wff ph
  let vw: setvar w
  let vt: setvar t
  let cA: class A
  let cQ: class Q
  let cT: class T
  let cU: class U
  let vh: setvar h
  let vi: setvar i
  let vm: setvar m
  let cG: class G
  let cJ: class J
  let cW: class W
  let cX: class X
  let cZ: class Z
  let vq: setvar q
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x
  assume stoweidlem35.1: |- F/ t ph
  assume stoweidlem35.2: |- F/ w ph
  assume stoweidlem35.3: |- F/ h ph
  assume stoweidlem35.4: |- Q = { h e. A | ( ( h ` Z ) = 0 /\ A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) ) }
  assume stoweidlem35.5: |- W = { w e. J | E. h e. Q w = { t e. T | 0 < ( h ` t ) } }
  assume stoweidlem35.6: |- G = ( w e. X |-> { h e. Q | w = { t e. T | 0 < ( h ` t ) } } )
  assume stoweidlem35.7: |- ( ph -> A e. _V )
  assume stoweidlem35.8: |- ( ph -> X e. Fin )
  assume stoweidlem35.9: |- ( ph -> X C_ W )
  assume stoweidlem35.10: |- ( ph -> ( T \ U ) C_ U. X )
  assume stoweidlem35.11: |- ( ph -> ( T \ U ) =/= (/) )

  disjoint h i
  disjoint h t
  disjoint h w
  disjoint i t
  disjoint i w
  disjoint t w
  disjoint i m
  disjoint i q
  disjoint m q
  disjoint m t
  disjoint q t
  disjoint G i
  disjoint Q w
  disjoint T h
  disjoint T w
  disjoint U q
  disjoint i ph
  disjoint m ph
  disjoint A h
  disjoint A t
  disjoint X h
  disjoint X i
  disjoint X t
  disjoint X w
  disjoint m w
  disjoint G m
  disjoint Q q
  disjoint T q
  disjoint Z t
  disjoint U w
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f t
  disjoint f w
  disjoint g h
  disjoint g i
  disjoint g t
  disjoint g w
  disjoint f k
  disjoint g k
  disjoint h k
  disjoint k t
  disjoint k w
  disjoint f l
  disjoint g l
  disjoint i l
  disjoint l t
  disjoint l w
  disjoint f m
  disjoint f q
  disjoint g m
  disjoint g q
  disjoint G f
  disjoint G g
  disjoint G l
  disjoint Q f
  disjoint Q g
  disjoint Q k
  disjoint T f
  disjoint T g
  disjoint U f
  disjoint U g
  disjoint f ph
  disjoint g ph
  disjoint k l
  disjoint k m
  disjoint G k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> E. m E. q ( m e. NN /\ ( q : ( 1 ... m ) --> Q /\ A. t e. ( T \ U ) E. i e. ( 1 ... m ) 0 < ( ( q ` i ) ` t ) ) ) )

  proof
    wph
    vm
    cv
    #
    cn
    wcel
    #
    c1
    @0
    cfz
    co
    #
    cQ
    vq
    cv
    #
    wf
    cc0
    vt
    cv
    #
    vi
    cv
    @3
    cfv
    cfv
    clt
    wbr
    vi
    @2
    wrex
    vt
    cT
    cU
    cdif
    #
    wral
    wa
    wa
    vq
    wex
    #
    vf
    wex
    vg
    wex
    #
    vm
    wex
    #
    @6
    vm
    wex
    wph
    @1
    vg
    cv
    #
    cG
    crn
    #
    wfn
    #
    vl
    cv
    #
    @9
    cfv
    #
    @12
    wcel
    #
    vl
    @10
    wral
    #
    @2
    @10
    vf
    cv
    #
    wf1o
    #
    w3a
    #
    wa
    #
    vf
    wex
    vg
    wex
    #
    vm
    wex
    #
    @8
    wph
    @1
    @11
    @15
    wa
    #
    @17
    wa
    #
    vf
    wex
    #
    vg
    wex
    #
    wa
    #
    vm
    wex
    #
    @21
    wph
    @25
    vm
    cn
    wrex
    #
    @27
    wph
    @22
    vg
    wex
    #
    @17
    vf
    wex
    #
    wa
    #
    vm
    cn
    wrex
    #
    @28
    wph
    @29
    vm
    cn
    wral
    @30
    vm
    cn
    wrex
    #
    @32
    wph
    @29
    vm
    cn
    wph
    @10
    cfn
    wcel
    #
    @29
    wph
    cX
    cfn
    wcel
    @34
    stoweidlem35.8
    vw
    cG
    cX
    vw
    cv
    #
    cc0
    @4
    vh
    cv
    #
    cfv
    #
    clt
    wbr
    #
    vt
    cT
    crab
    #
    wceq
    #
    vh
    cQ
    crab
    #
    stoweidlem35.6
    rnmptfi
    syl
    #
    wph
    @34
    wa
    #
    @11
    @12
    c0
    wne
    #
    @14
    wi
    #
    vl
    @10
    wral
    #
    wa
    #
    vg
    wex
    #
    @29
    @34
    @48
    wph
    vl
    @10
    vg
    fnchoice
    adantl
    @43
    @47
    @22
    vg
    wph
    @47
    @22
    wi
    @34
    wph
    @47
    @22
    wph
    @47
    wa
    #
    @11
    @15
    wph
    @11
    @46
    simprl
    @49
    vk
    cv
    #
    @9
    cfv
    #
    @50
    wcel
    #
    vk
    @10
    wral
    @15
    @49
    @52
    vk
    @10
    @49
    @50
    @10
    wcel
    #
    wa
    @50
    c0
    wne
    #
    @52
    wph
    @53
    @54
    @47
    wph
    @53
    wa
    #
    @36
    @50
    wcel
    #
    vh
    wex
    #
    @54
    @55
    @50
    @41
    wceq
    #
    @57
    vw
    cX
    wph
    @53
    vw
    stoweidlem35.2
    vw
    vk
    @10
    vw
    cG
    vw
    cG
    vw
    cX
    @41
    cmpt
    #
    stoweidlem35.6
    vw
    cX
    @41
    nfmpt1
    nfcxfr
    nfrn
    #
    nfcri
    nfan
    wph
    @35
    cX
    wcel
    #
    @58
    @57
    @53
    wph
    @61
    wa
    #
    @58
    wa
    #
    @36
    @41
    wcel
    #
    vh
    wex
    #
    @57
    @62
    @65
    @58
    @62
    @36
    cQ
    wcel
    @40
    wa
    #
    vh
    wex
    #
    @65
    @62
    @40
    vh
    cQ
    wrex
    #
    @67
    @62
    @35
    cJ
    wcel
    #
    @68
    @62
    @35
    @68
    vw
    cJ
    crab
    #
    wcel
    @69
    @68
    wa
    @62
    @35
    cW
    @70
    wph
    cX
    cW
    @35
    stoweidlem35.9
    sselda
    stoweidlem35.5
    syl6eleq
    @68
    vw
    cJ
    rabid
    sylib
    simprd
    @40
    vh
    cQ
    df-rex
    sylib
    @64
    @66
    vh
    @40
    vh
    cQ
    rabid
    exbii
    sylibr
    adantr
    @63
    @64
    @56
    vh
    @62
    @58
    vh
    wph
    @61
    vh
    stoweidlem35.3
    @61
    vh
    nfv
    nfan
    vh
    @50
    @41
    @40
    vh
    cQ
    nfrab1
    nfeq2
    nfan
    @58
    @64
    @56
    wi
    @62
    @58
    @56
    @64
    @50
    @41
    @36
    eleq2
    biimprd
    adantl
    eximd
    mpd
    adantllr
    @53
    @58
    vw
    cX
    wrex
    #
    wph
    @53
    @71
    vw
    cX
    @41
    @50
    cG
    @10
    stoweidlem35.6
    elrnmpt
    ibi
    adantl
    r19.29af
    vh
    @50
    n0
    sylibr
    adantlr
    @49
    @53
    @46
    @54
    @52
    wi
    #
    wph
    @11
    @46
    @53
    simplrr
    @45
    @72
    vl
    @50
    @10
    @12
    @50
    wceq
    #
    @44
    @54
    @14
    @52
    @12
    @50
    c0
    neeq1
    @73
    @14
    @51
    @12
    wcel
    @52
    @73
    @13
    @51
    @12
    @12
    @50
    @9
    fveq2
    eleq1d
    @12
    @50
    @51
    eleq2
    bitrd
    #
    imbi12d
    rspccva
    sylancom
    mpd
    ralrimiva
    @52
    @14
    vk
    vl
    @10
    @50
    @12
    wceq
    #
    @52
    @13
    @50
    wcel
    @14
    @75
    @51
    @13
    @50
    @50
    @12
    @9
    fveq2
    eleq1d
    @50
    @12
    @13
    eleq2
    bitrd
    cbvralv
    sylib
    jca
    ex
    adantr
    eximdv
    mpd
    mpdan
    ralrimivw
    wph
    @10
    chash
    cfv
    #
    cn
    wcel
    c1
    @76
    cfz
    co
    #
    @10
    @16
    wf1o
    #
    vf
    wex
    #
    wa
    #
    @33
    wph
    @10
    c0
    wceq
    #
    wn
    @80
    wph
    @81
    cX
    c0
    wceq
    #
    wph
    cX
    cuni
    #
    c0
    wceq
    @82
    wph
    @83
    c0
    wph
    @5
    @83
    wss
    #
    @5
    c0
    wne
    @83
    c0
    wne
    stoweidlem35.10
    stoweidlem35.11
    @5
    @83
    ssn0
    syl2anc
    neneqd
    @82
    @83
    c0
    cuni
    c0
    cX
    c0
    unieq
    uni0
    syl6eq
    nsyl
    @81
    cG
    cdm
    #
    c0
    wceq
    wph
    @82
    cG
    dm0rn0
    wph
    @85
    cX
    c0
    wph
    cG
    cX
    wfn
    #
    @85
    cX
    wceq
    wph
    cX
    cvv
    cG
    wf
    @86
    wph
    vw
    cX
    @41
    cvv
    cG
    stoweidlem35.2
    wph
    @41
    cvv
    wcel
    #
    @61
    wph
    cQ
    cvv
    wcel
    #
    @87
    wph
    cZ
    @36
    cfv
    cc0
    wceq
    #
    cc0
    @37
    cle
    wbr
    @37
    c1
    cle
    wbr
    wa
    #
    vt
    cT
    wral
    #
    wa
    #
    vh
    cA
    cQ
    cvv
    stoweidlem35.4
    stoweidlem35.7
    rabexd
    #
    @40
    vh
    cQ
    cvv
    vh
    cQ
    @92
    vh
    cA
    crab
    #
    stoweidlem35.4
    @92
    vh
    cA
    nfrab1
    nfcxfr
    #
    rabexgf
    syl
    adantr
    stoweidlem35.6
    fmptdf
    cX
    cG
    dffn2
    sylibr
    cX
    cG
    fndm
    syl
    eqeq1d
    syl5bbr
    mtbird
    wph
    @81
    @80
    wph
    @34
    @81
    @80
    wo
    @42
    @10
    vf
    fz1f1o
    syl
    ord
    mpd
    @30
    @79
    vm
    @76
    cn
    @0
    @76
    wceq
    #
    @17
    @78
    vf
    @96
    @2
    @77
    wceq
    @17
    @78
    wb
    @0
    @76
    c1
    cfz
    oveq2
    @2
    @77
    @10
    @16
    f1oeq2
    syl
    exbidv
    rspcev
    syl
    @29
    @30
    vm
    cn
    r19.29
    syl2anc
    wph
    @31
    @25
    vm
    cn
    @31
    @25
    wi
    wph
    @25
    @31
    @22
    @17
    vg
    vf
    eeanv
    biimpri
    a1i
    reximdv
    mpd
    @25
    vm
    cn
    df-rex
    sylib
    wph
    @26
    @20
    vm
    @26
    @20
    wi
    wph
    @26
    @1
    @23
    wa
    #
    vf
    wex
    #
    vg
    wex
    #
    @20
    @26
    @1
    @24
    wa
    #
    vg
    wex
    #
    @99
    @1
    @1
    vg
    wal
    @25
    @101
    @1
    vg
    ax-5
    @1
    @24
    vg
    19.29
    sylan
    @100
    @98
    vg
    @1
    @1
    vf
    wal
    @24
    @98
    @1
    vf
    ax-5
    @1
    @23
    vf
    19.29
    sylan
    eximi
    syl
    @19
    @97
    vg
    vf
    @18
    @23
    @1
    @11
    @15
    @17
    df-3an
    anbi2i
    2exbii
    sylibr
    a1i
    eximdv
    mpd
    wph
    @20
    @7
    vm
    wph
    @19
    @6
    vg
    vf
    wph
    @19
    @6
    wph
    @19
    wa
    #
    vw
    vt
    cQ
    cT
    cU
    vh
    vi
    @16
    cG
    @0
    cX
    @9
    vq
    vk
    stoweidlem35.6
    wph
    @88
    @19
    @93
    adantr
    wph
    @1
    @18
    simprl
    @11
    @15
    @17
    @1
    wph
    simprr1
    wph
    @10
    cvv
    wcel
    #
    @19
    wph
    @34
    @103
    @42
    @10
    cfn
    elex
    syl
    adantr
    @102
    @15
    @53
    @52
    @11
    @15
    @17
    @1
    wph
    simprr2
    @14
    @52
    vl
    @50
    @10
    @74
    rspccva
    sylan
    @11
    @15
    @17
    @1
    wph
    simprr3
    wph
    @84
    @19
    stoweidlem35.10
    adantr
    wph
    @19
    vt
    stoweidlem35.1
    @1
    @18
    vt
    @1
    vt
    nfv
    @11
    @15
    @17
    vt
    vt
    @10
    @9
    vt
    @9
    nfcv
    vt
    cG
    vt
    cG
    @59
    stoweidlem35.6
    vt
    vw
    cX
    @41
    vt
    cX
    nfcv
    @40
    vt
    vh
    cQ
    vt
    @35
    @39
    @38
    vt
    cT
    nfrab1
    nfeq2
    vt
    cQ
    @94
    stoweidlem35.4
    @92
    vt
    vh
    cA
    @89
    @91
    vt
    @89
    vt
    nfv
    @90
    vt
    cT
    nfra1
    nfan
    vt
    cA
    nfcv
    nfrab
    nfcxfr
    nfrab
    nfmpt
    nfcxfr
    nfrn
    #
    nffn
    @14
    vt
    vl
    @10
    @104
    @14
    vt
    nfv
    nfral
    vt
    @2
    @10
    @16
    vt
    @16
    nfcv
    vt
    @2
    nfcv
    @104
    nff1o
    nf3an
    nfan
    nfan
    wph
    @19
    vw
    stoweidlem35.2
    @1
    @18
    vw
    @1
    vw
    nfv
    @11
    @15
    @17
    vw
    vw
    @10
    @9
    vw
    @9
    nfcv
    @60
    nffn
    @14
    vw
    vl
    @10
    @60
    @14
    vw
    nfv
    nfral
    vw
    @2
    @10
    @16
    vw
    @16
    nfcv
    vw
    @2
    nfcv
    @60
    nff1o
    nf3an
    nfan
    nfan
    @95
    stoweidlem27
    ex
    2eximdv
    eximdv
    mpd
    @7
    @6
    vm
    @6
    @6
    vg
    vf
    @6
    id
    exlimivv
    eximi
    syl
end
