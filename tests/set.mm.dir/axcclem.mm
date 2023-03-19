include "cv.mm"
include "com.mm"
include "cen.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "cdom.mm"
include "csdm.mm"
include "wn.mm"
include "wa.mm"
include "cfn.mm"
include "isfinite2.mm"
include "csn.mm"
include "cdif.mm"
include "eleq1i.mm"
include "cun.mm"
include "wss.mm"
include "undif1.mm"
include "snfi.mm"
include "unfi.mm"
include "mpan2.mm"
include "syl5eqelr.mm"
include "ssun1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "sylbi.mm"
include "cvv.mm"
include "wb.mm"
include "dcomex.mm"
include "isfiniteg.mm"
include "ax-mp.mm"
include "sdomnen.mm"
include "3syl.mm"
include "con2i.mm"
include "sdomentr.mm"
include "expcom.mm"
include "mtod.mm"
include "vex.mm"
include "difss.mm"
include "eqsstri.mm"
include "ssdomg.mm"
include "mp2.mm"
include "jctil.mm"
include "bren2.mm"
include "sylibr.mm"
include "entr.mm"
include "mpancom.mm"
include "ensym.mm"
include "wf1o.mm"
include "bren.mm"
include "cuni.mm"
include "wf.mm"
include "csuc.mm"
include "co.mm"
include "f1of.mm"
include "peano1.mm"
include "ffvelrn.mm"
include "eldifn.mm"
include "eleq2s.mm"
include "wceq.mm"
include "fvex.mm"
include "elsn.mm"
include "notbii.mm"
include "neq0.mm"
include "bitr2i.mm"
include "syl.mm"
include "w3a.mm"
include "cxp.mm"
include "cpw.mm"
include "elunii.mm"
include "sylan2.mm"
include "ffvelrnda.mm"
include "difabs.mm"
include "difeq1i.mm"
include "3eqtr4i.mm"
include "pwuni.mm"
include "ssdif.mm"
include "eqsstr3i.mm"
include "sseli.mm"
include "ralrimivw.mm"
include "ralrimiva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "adantl.mm"
include "difexg.mm"
include "eqeltri.mm"
include "uniex.mm"
include "axdc4.mm"
include "syl2anc.mm"
include "3simpb.mm"
include "eximi.mm"
include "ex.mm"
include "exlimiv.mm"
include "mpcom.mm"
include "velsn.mm"
include "necon3bbii.mm"
include "eleq2i.mm"
include "eldif.mm"
include "sylbbr.mm"
include "sylan2br.mm"
include "simpl.mm"
include "wrex.mm"
include "wfo.mm"
include "f1ofo.mm"
include "foelrn.mm"
include "sylan.mm"
include "ccnv.mm"
include "suceq.mm"
include "fveq2d.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "3adant3.mm"
include "eqcom.mm"
include "f1ocnvfv.mm"
include "syl5bi.mm"
include "3adant1.mm"
include "eqcomd.mm"
include "3adant2.mm"
include "simpr.mm"
include "eqidd.mm"
include "ovmpt2.mm"
include "3ad2ant1.mm"
include "3eltr3d.mm"
include "eleq1.mm"
include "mpbird.mm"
include "fvmpt.mm"
include "simp3.mm"
include "3eltr4d.mm"
include "3exp.mm"
include "com3r.mm"
include "3expd.mm"
include "com4r.mm"
include "rexlimiv.mm"
include "mpid.mm"
include "impd.mm"
include "impancom.mm"
include "syl5.mm"
include "expd.mm"
include "ralrimiv.mm"
include "cmpt.mm"
include "crn.mm"
include "fvrn0.mm"
include "rgenw.mm"
include "eqid.mm"
include "fmpt.mm"
include "mpbi.mm"
include "rnex.mm"
include "p0ex.mm"
include "unex.mm"
include "fex2.mm"
include "mp3an.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "spcev.mm"
include "exlimddv.mm"

theorem axcclem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vc: setvar c
  let vi: setvar i
  let vk: setvar k
  assume axcclem.1: |- A = ( x \ { (/) } )
  assume axcclem.2: |- F = ( n e. _om , y e. U. A |-> ( f ` n ) )
  assume axcclem.3: |- G = ( w e. A |-> ( h ` suc ( `' f ` w ) ) )

  disjoint A f
  disjoint A h
  disjoint f h
  disjoint A n
  disjoint A y
  disjoint f n
  disjoint f y
  disjoint h n
  disjoint h y
  disjoint n y
  disjoint A w
  disjoint A z
  disjoint f w
  disjoint f z
  disjoint h w
  disjoint h z
  disjoint w z
  disjoint F h
  disjoint F z
  disjoint G g
  disjoint G z
  disjoint g z
  disjoint f g
  disjoint f x
  disjoint g h
  disjoint g x
  disjoint h x
  disjoint A c
  disjoint c f
  disjoint c h
  disjoint A i
  disjoint f i
  disjoint h i
  disjoint i n
  disjoint i y
  disjoint A k
  disjoint c k
  disjoint h k
  disjoint F c
  disjoint F k
  disjoint F i
  disjoint i k
  disjoint i z
  disjoint k z
  disjoint G i
  assert |- ( x ~~ _om -> E. g A. z e. x ( z =/= (/) -> ( g ` z ) e. z ) )

  proof
    vx
    cv
    #
    com
    cen
    wbr
    #
    cA
    com
    cen
    wbr
    #
    com
    cA
    cen
    wbr
    #
    vz
    cv
    #
    c0
    wne
    #
    @4
    vg
    cv
    #
    cfv
    #
    @4
    wcel
    #
    wi
    #
    vz
    @0
    wral
    #
    vg
    wex
    #
    cA
    @0
    cen
    wbr
    #
    @1
    @2
    @1
    cA
    @0
    cdom
    wbr
    #
    cA
    @0
    csdm
    wbr
    #
    wn
    #
    wa
    @12
    @1
    @15
    @13
    @1
    @14
    cA
    com
    csdm
    wbr
    #
    @16
    @1
    @16
    cA
    cfn
    wcel
    #
    @0
    cfn
    wcel
    #
    @1
    wn
    #
    cA
    isfinite2
    @17
    @0
    c0
    csn
    #
    cdif
    #
    cfn
    wcel
    #
    @18
    cA
    @21
    cfn
    axcclem.1
    eleq1i
    @22
    @0
    @20
    cun
    #
    cfn
    wcel
    @0
    @23
    wss
    @18
    @22
    @23
    @21
    @20
    cun
    #
    cfn
    @0
    @20
    undif1
    @22
    @20
    cfn
    wcel
    @24
    cfn
    wcel
    c0
    snfi
    @21
    @20
    unfi
    mpan2
    syl5eqelr
    @0
    @20
    ssun1
    @23
    @0
    ssfi
    sylancl
    sylbi
    @18
    @0
    com
    csdm
    wbr
    #
    @19
    com
    cvv
    wcel
    @18
    @25
    wb
    dcomex
    @0
    isfiniteg
    ax-mp
    @0
    com
    sdomnen
    sylbi
    3syl
    con2i
    @14
    @1
    @16
    cA
    @0
    com
    sdomentr
    expcom
    mtod
    @0
    cvv
    wcel
    #
    cA
    @0
    wss
    @13
    vx
    vex
    #
    cA
    @21
    @0
    axcclem.1
    @0
    @20
    difss
    eqsstri
    cA
    @0
    cvv
    ssdomg
    mp2
    jctil
    cA
    @0
    bren2
    sylibr
    cA
    @0
    com
    entr
    mpancom
    cA
    com
    ensym
    @3
    com
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @11
    com
    cA
    vf
    bren
    @29
    @11
    vf
    @29
    com
    cA
    cuni
    #
    vh
    cv
    #
    wf
    #
    vk
    cv
    #
    csuc
    #
    @31
    cfv
    #
    @33
    @33
    @31
    cfv
    #
    cF
    co
    #
    wcel
    #
    vk
    com
    wral
    #
    wa
    #
    @11
    vh
    vc
    cv
    #
    c0
    @28
    cfv
    #
    wcel
    #
    vc
    wex
    #
    @29
    @40
    vh
    wex
    #
    @29
    @42
    cA
    wcel
    #
    @44
    @29
    com
    cA
    @28
    wf
    c0
    com
    wcel
    @46
    com
    cA
    @28
    f1of
    #
    peano1
    com
    cA
    c0
    @28
    ffvelrn
    sylancl
    #
    @46
    @42
    @20
    wcel
    #
    wn
    #
    @44
    @50
    @42
    @21
    cA
    @42
    @0
    @20
    eldifn
    axcclem.1
    eleq2s
    @50
    @42
    c0
    wceq
    #
    wn
    @44
    @49
    @51
    @42
    c0
    c0
    @28
    fvex
    elsn
    notbii
    vc
    @42
    neq0
    bitr2i
    sylibr
    syl
    @43
    @29
    @45
    wi
    vc
    @43
    @29
    @45
    @43
    @29
    wa
    #
    @32
    c0
    @31
    cfv
    @41
    wceq
    #
    @39
    w3a
    #
    vh
    wex
    #
    @45
    @52
    @41
    @30
    wcel
    #
    com
    @30
    cxp
    @30
    cpw
    #
    @20
    cdif
    #
    cF
    wf
    #
    @55
    @29
    @43
    @46
    @56
    @48
    @41
    @42
    cA
    elunii
    sylan2
    @29
    @59
    @43
    @29
    vn
    cv
    #
    @28
    cfv
    #
    @58
    wcel
    #
    vy
    @30
    wral
    #
    vn
    com
    wral
    @59
    @29
    @63
    vn
    com
    @29
    @60
    com
    wcel
    wa
    @61
    cA
    wcel
    #
    @63
    @29
    com
    cA
    @60
    @28
    @47
    ffvelrnda
    @64
    @62
    vy
    @30
    cA
    @58
    @61
    cA
    cA
    @20
    cdif
    #
    @58
    @21
    @20
    cdif
    @21
    @65
    cA
    @0
    @20
    difabs
    cA
    @21
    @20
    axcclem.1
    difeq1i
    axcclem.1
    3eqtr4i
    cA
    @57
    wss
    @65
    @58
    wss
    cA
    pwuni
    cA
    @57
    @20
    ssdif
    ax-mp
    eqsstr3i
    sseli
    ralrimivw
    syl
    ralrimiva
    vn
    vy
    com
    @30
    @61
    @58
    cF
    axcclem.2
    fmpt2
    sylib
    adantl
    @30
    @41
    vh
    vk
    cF
    cA
    cA
    @21
    cvv
    axcclem.1
    @26
    @21
    cvv
    wcel
    @27
    @0
    @20
    cvv
    difexg
    ax-mp
    eqeltri
    #
    uniex
    axdc4
    syl2anc
    @54
    @40
    vh
    @32
    @53
    @39
    3simpb
    eximi
    syl
    ex
    exlimiv
    mpcom
    @29
    @40
    wa
    #
    @5
    @4
    cG
    cfv
    #
    @4
    wcel
    #
    wi
    #
    vz
    @0
    wral
    #
    @11
    @67
    @70
    vz
    @0
    @67
    @4
    @0
    wcel
    #
    @5
    @69
    @72
    @5
    wa
    @4
    cA
    wcel
    #
    @67
    @69
    @5
    @72
    @4
    @20
    wcel
    #
    wn
    #
    @73
    @74
    @4
    c0
    vz
    c0
    velsn
    necon3bbii
    @73
    @4
    @21
    wcel
    @72
    @75
    wa
    cA
    @21
    @4
    axcclem.1
    eleq2i
    @4
    @0
    @20
    eldif
    sylbbr
    sylan2br
    @29
    @73
    @40
    @69
    @29
    @73
    wa
    #
    @32
    @39
    @69
    @76
    @32
    @29
    @39
    @69
    wi
    #
    @29
    @73
    simpl
    @76
    @4
    vi
    cv
    #
    @28
    cfv
    #
    wceq
    #
    vi
    com
    wrex
    #
    @32
    @29
    @77
    wi
    wi
    #
    @29
    com
    cA
    @28
    wfo
    @73
    @81
    com
    cA
    @28
    f1ofo
    vi
    com
    cA
    @4
    @28
    foelrn
    sylan
    @80
    @82
    vi
    com
    @80
    @32
    @29
    @78
    com
    wcel
    #
    @77
    @80
    @32
    @29
    @83
    @77
    @32
    @29
    @83
    w3a
    #
    @39
    @80
    @69
    @84
    @39
    @80
    @69
    @84
    @39
    @80
    w3a
    #
    @4
    @28
    ccnv
    #
    cfv
    #
    csuc
    #
    @31
    cfv
    #
    @79
    @68
    @4
    @85
    @78
    csuc
    #
    @31
    cfv
    #
    @78
    @78
    @31
    cfv
    #
    cF
    co
    #
    @89
    @79
    @84
    @39
    @91
    @93
    wcel
    #
    @80
    @84
    @39
    @94
    @83
    @32
    @39
    @94
    wi
    @29
    @38
    @94
    vk
    @78
    com
    @33
    @78
    wceq
    #
    @35
    @91
    @37
    @93
    @95
    @34
    @90
    @31
    @33
    @78
    suceq
    fveq2d
    @95
    @33
    @78
    @36
    @92
    cF
    @95
    id
    @33
    @78
    @31
    fveq2
    oveq12d
    eleq12d
    rspcv
    3ad2ant3
    imp
    3adant3
    @85
    @90
    @88
    @31
    @85
    @78
    @87
    wceq
    #
    @90
    @88
    wceq
    @84
    @80
    @96
    @39
    @84
    @80
    wa
    @87
    @78
    @84
    @80
    @87
    @78
    wceq
    #
    @29
    @83
    @80
    @97
    wi
    @32
    @80
    @79
    @4
    wceq
    @29
    @83
    wa
    @97
    @4
    @79
    eqcom
    com
    cA
    @78
    @4
    @28
    f1ocnvfv
    syl5bi
    3adant1
    imp
    eqcomd
    3adant2
    @78
    @87
    suceq
    syl
    fveq2d
    @84
    @39
    @93
    @79
    wceq
    #
    @80
    @32
    @83
    @98
    @29
    @32
    @83
    wa
    @83
    @92
    @30
    wcel
    @98
    @32
    @83
    simpr
    com
    @30
    @78
    @31
    ffvelrn
    vn
    vy
    @78
    @92
    com
    @30
    @61
    @79
    cF
    @79
    @60
    @78
    @28
    fveq2
    vy
    cv
    @92
    wceq
    @79
    eqidd
    axcclem.2
    @78
    @28
    fvex
    ovmpt2
    syl2anc
    3adant2
    3ad2ant1
    3eltr3d
    @85
    @73
    @68
    @89
    wceq
    @85
    @73
    @79
    cA
    wcel
    #
    @84
    @39
    @99
    @80
    @29
    @83
    @99
    @32
    @29
    com
    cA
    @78
    @28
    @47
    ffvelrnda
    3adant1
    3ad2ant1
    @80
    @84
    @73
    @99
    wb
    @39
    @4
    @79
    cA
    eleq1
    3ad2ant3
    mpbird
    vw
    @4
    vw
    cv
    #
    @86
    cfv
    #
    csuc
    #
    @31
    cfv
    #
    @89
    cA
    cG
    @100
    @4
    wceq
    #
    @102
    @88
    @31
    @104
    @101
    @87
    wceq
    @102
    @88
    wceq
    @100
    @4
    @86
    fveq2
    @101
    @87
    suceq
    syl
    fveq2d
    axcclem.3
    @88
    @31
    fvex
    fvmpt
    syl
    @84
    @39
    @80
    simp3
    3eltr4d
    3exp
    com3r
    3expd
    com4r
    rexlimiv
    syl
    mpid
    impd
    impancom
    syl5
    expd
    ralrimiv
    @10
    @71
    vg
    cG
    cG
    vw
    cA
    @103
    cmpt
    #
    cvv
    axcclem.3
    cA
    @31
    crn
    #
    @20
    cun
    #
    @105
    wf
    #
    cA
    cvv
    wcel
    @107
    cvv
    wcel
    @105
    cvv
    wcel
    @103
    @107
    wcel
    #
    vw
    cA
    wral
    @108
    @109
    vw
    cA
    @31
    @102
    fvrn0
    rgenw
    vw
    cA
    @107
    @103
    @105
    @105
    eqid
    fmpt
    mpbi
    @66
    @106
    @20
    @31
    vh
    vex
    rnex
    p0ex
    unex
    cA
    @107
    @105
    cvv
    cvv
    fex2
    mp3an
    eqeltri
    @6
    cG
    wceq
    #
    @9
    @70
    vz
    @0
    @110
    @8
    @69
    @5
    @110
    @7
    @68
    @4
    @4
    @6
    cG
    fveq1
    eleq1d
    imbi2d
    ralbidv
    spcev
    syl
    exlimddv
    exlimiv
    sylbi
    3syl
end
