include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wf1o.mm"
include "cfv.mm"
include "wne.mm"
include "wral.mm"
include "cab.mm"
include "chash.mm"
include "cle.mm"
include "cdom.mm"
include "wex.mm"
include "simpl.mm"
include "bren.mm"
include "sylib.mm"
include "deranglem.mm"
include "adantl.mm"
include "wi.mm"
include "ccom.mm"
include "ccnv.mm"
include "f1oco.mm"
include "ad2ant2lr.mm"
include "f1ocnv.mm"
include "ad2antlr.mm"
include "syl2anc.mm"
include "coass.mm"
include "fveq1i.mm"
include "wf.mm"
include "wceq.mm"
include "simprl.mm"
include "f1of.mm"
include "syl.mm"
include "fvco3.mm"
include "sylan.mm"
include "syl5eq.mm"
include "ffvelrnda.mm"
include "simplrr.mm"
include "fveq2.mm"
include "id.mm"
include "neeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqnetrd.mm"
include "necomd.mm"
include "simpllr.mm"
include "f1ocnvfv.mm"
include "necon3d.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "cbvralv.mm"
include "jca.mm"
include "ex.mm"
include "vex.mm"
include "f1oeq1.mm"
include "fveq1.mm"
include "neeq1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "elab.mm"
include "coex.mm"
include "cnvex.mm"
include "3imtr4g.mm"
include "wb.mm"
include "anbi12i.mm"
include "wfo.mm"
include "wfn.mm"
include "f1ofo.mm"
include "adantrr.mm"
include "f1ofn.mm"
include "simplr.mm"
include "simprrl.mm"
include "cocan2.mm"
include "syl3anc.mm"
include "wf1.mm"
include "f1of1.mm"
include "simprll.mm"
include "cocan1.mm"
include "bitrd.mm"
include "syl5bi.mm"
include "dom2d.mm"
include "exlimdv.mm"
include "mp2d.mm"
include "enfii.mm"
include "ancoms.mm"
include "hashdom.mm"
include "mpbird.mm"
include "derangval.mm"
include "3brtr4d.mm"

theorem derangenlem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vz: setvar z
  let vb: setvar b
  let vc: setvar c
  let cF: class F
  let vk: setvar k
  let cN: class N
  let cC: class C
  let wph: wff ph
  let cK: class K
  let cM: class M
  let cS: class S
  let cV: class V
  assume derang.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )

  disjoint f x
  disjoint f y
  disjoint A f
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint f g
  disjoint f h
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint f z
  disjoint g h
  disjoint g m
  disjoint g n
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h m
  disjoint h n
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint F b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint F c
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint c h
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c z
  disjoint N c
  disjoint f k
  disjoint N f
  disjoint g k
  disjoint N g
  disjoint h k
  disjoint N h
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b h
  disjoint b s
  disjoint b z
  disjoint B b
  disjoint c s
  disjoint B c
  disjoint B g
  disjoint B h
  disjoint B s
  disjoint B z
  disjoint C b
  disjoint C c
  disjoint C x
  disjoint C y
  disjoint b ph
  disjoint c ph
  disjoint ph x
  disjoint ph y
  disjoint D n
  disjoint K c
  disjoint K f
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint M b
  disjoint M f
  disjoint M g
  disjoint M x
  disjoint M y
  disjoint S m
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint V f
  assert |- ( ( A ~~ B /\ B e. Fin ) -> ( D ` A ) <_ ( D ` B ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cA
    cA
    vf
    cv
    #
    wf1o
    #
    vy
    cv
    #
    @3
    cfv
    #
    @5
    wne
    #
    vy
    cA
    wral
    #
    wa
    #
    vf
    cab
    #
    chash
    cfv
    #
    cB
    cB
    @3
    wf1o
    #
    @7
    vy
    cB
    wral
    #
    wa
    #
    vf
    cab
    #
    chash
    cfv
    #
    cA
    cD
    cfv
    #
    cB
    cD
    cfv
    #
    cle
    @2
    @11
    @16
    cle
    wbr
    #
    @10
    @15
    cdom
    wbr
    #
    @2
    cA
    cB
    vs
    cv
    #
    wf1o
    #
    vs
    wex
    #
    @15
    cfn
    wcel
    #
    @20
    @2
    @0
    @23
    @0
    @1
    simpl
    cA
    cB
    vs
    bren
    sylib
    @1
    @24
    @0
    @13
    cB
    vf
    deranglem
    adantl
    #
    @2
    @22
    @24
    @20
    wi
    #
    vs
    @2
    @22
    @26
    @2
    @22
    wa
    #
    vg
    vh
    @10
    @15
    @21
    vg
    cv
    #
    ccom
    #
    @21
    ccnv
    #
    ccom
    #
    @21
    vh
    cv
    #
    ccom
    #
    @30
    ccom
    #
    cfn
    @27
    cA
    cA
    @28
    wf1o
    #
    @5
    @28
    cfv
    #
    @5
    wne
    #
    vy
    cA
    wral
    #
    wa
    #
    cB
    cB
    @31
    wf1o
    #
    @5
    @31
    cfv
    #
    @5
    wne
    #
    vy
    cB
    wral
    #
    wa
    #
    @28
    @10
    wcel
    #
    @31
    @15
    wcel
    @27
    @39
    @44
    @27
    @39
    wa
    #
    @40
    @43
    @46
    cA
    cB
    @29
    wf1o
    #
    cB
    cA
    @30
    wf1o
    #
    @40
    @22
    @35
    @47
    @2
    @38
    cA
    cA
    cB
    @21
    @28
    f1oco
    ad2ant2lr
    #
    @22
    @48
    @2
    @39
    cA
    cB
    @21
    f1ocnv
    #
    ad2antlr
    #
    cB
    cA
    cB
    @29
    @30
    f1oco
    syl2anc
    @46
    vz
    cv
    #
    @31
    cfv
    #
    @52
    wne
    #
    vz
    cB
    wral
    @43
    @46
    @54
    vz
    cB
    @46
    @52
    cB
    wcel
    #
    wa
    #
    @53
    @52
    @28
    @30
    ccom
    #
    cfv
    #
    @21
    cfv
    #
    @52
    @56
    @53
    @52
    @21
    @57
    ccom
    #
    cfv
    #
    @59
    @52
    @31
    @60
    @21
    @28
    @30
    coass
    fveq1i
    @46
    cB
    cA
    @57
    wf
    #
    @55
    @61
    @59
    wceq
    @46
    cB
    cA
    @57
    wf1o
    #
    @62
    @46
    @35
    @48
    @63
    @27
    @35
    @38
    simprl
    @51
    cB
    cA
    cA
    @28
    @30
    f1oco
    syl2anc
    cB
    cA
    @57
    f1of
    syl
    #
    cB
    cA
    @52
    @21
    @57
    fvco3
    sylan
    syl5eq
    @56
    @52
    @30
    cfv
    #
    @58
    wne
    @59
    @52
    wne
    @56
    @58
    @65
    @56
    @58
    @65
    @28
    cfv
    #
    @65
    @46
    cB
    cA
    @30
    wf
    #
    @55
    @58
    @66
    wceq
    @46
    @48
    @67
    @51
    cB
    cA
    @30
    f1of
    syl
    #
    cB
    cA
    @52
    @28
    @30
    fvco3
    sylan
    @56
    @65
    cA
    wcel
    @38
    @66
    @65
    wne
    #
    @46
    cB
    cA
    @52
    @30
    @68
    ffvelrnda
    @27
    @35
    @38
    @55
    simplrr
    @37
    @69
    vy
    @65
    cA
    @5
    @65
    wceq
    #
    @36
    @66
    @5
    @65
    @5
    @65
    @28
    fveq2
    @70
    id
    neeq12d
    rspcv
    sylc
    eqnetrd
    necomd
    @56
    @59
    @52
    @65
    @58
    @56
    @22
    @58
    cA
    wcel
    @59
    @52
    wceq
    @65
    @58
    wceq
    wi
    @2
    @22
    @39
    @55
    simpllr
    @46
    cB
    cA
    @52
    @57
    @64
    ffvelrnda
    cA
    cB
    @58
    @52
    @21
    f1ocnvfv
    syl2anc
    necon3d
    mpd
    eqnetrd
    ralrimiva
    @54
    @42
    vz
    vy
    cB
    @52
    @5
    wceq
    #
    @53
    @41
    @52
    @5
    @52
    @5
    @31
    fveq2
    @71
    id
    neeq12d
    cbvralv
    sylib
    jca
    ex
    @9
    @39
    vf
    @28
    vg
    vex
    #
    @3
    @28
    wceq
    #
    @4
    @35
    @8
    @38
    cA
    cA
    @3
    @28
    f1oeq1
    @73
    @7
    @37
    vy
    cA
    @73
    @6
    @36
    @5
    @5
    @3
    @28
    fveq1
    neeq1d
    ralbidv
    anbi12d
    elab
    #
    @14
    @44
    vf
    @31
    @29
    @30
    @21
    @28
    vs
    vex
    #
    @72
    coex
    @21
    @75
    cnvex
    coex
    @3
    @31
    wceq
    #
    @12
    @40
    @13
    @43
    cB
    cB
    @3
    @31
    f1oeq1
    @76
    @7
    @42
    vy
    cB
    @76
    @6
    @41
    @5
    @5
    @3
    @31
    fveq1
    neeq1d
    ralbidv
    anbi12d
    elab
    3imtr4g
    @45
    @32
    @10
    wcel
    #
    wa
    @39
    cA
    cA
    @32
    wf1o
    #
    @5
    @32
    cfv
    #
    @5
    wne
    #
    vy
    cA
    wral
    #
    wa
    #
    wa
    #
    @27
    @31
    @34
    wceq
    #
    @28
    @32
    wceq
    #
    wb
    #
    @45
    @39
    @77
    @82
    @74
    @9
    @82
    vf
    @32
    vh
    vex
    @3
    @32
    wceq
    #
    @4
    @78
    @8
    @81
    cA
    cA
    @3
    @32
    f1oeq1
    @87
    @7
    @80
    vy
    cA
    @87
    @6
    @79
    @5
    @5
    @3
    @32
    fveq1
    neeq1d
    ralbidv
    anbi12d
    elab
    anbi12i
    @27
    @83
    @86
    @27
    @83
    wa
    #
    @84
    @29
    @33
    wceq
    #
    @85
    @88
    cB
    cA
    @30
    wfo
    #
    @29
    cA
    wfn
    #
    @33
    cA
    wfn
    #
    @84
    @89
    wb
    @88
    @48
    @90
    @22
    @48
    @2
    @83
    @50
    ad2antlr
    cB
    cA
    @30
    f1ofo
    syl
    @88
    @47
    @91
    @27
    @39
    @47
    @82
    @49
    adantrr
    cA
    cB
    @29
    f1ofn
    syl
    @88
    cA
    cB
    @33
    wf1o
    #
    @92
    @88
    @22
    @78
    @93
    @2
    @22
    @83
    simplr
    @27
    @39
    @78
    @81
    simprrl
    #
    cA
    cA
    cB
    @21
    @32
    f1oco
    syl2anc
    cA
    cB
    @33
    f1ofn
    syl
    cB
    cA
    @30
    @29
    @33
    cocan2
    syl3anc
    @88
    cA
    cB
    @21
    wf1
    #
    cA
    cA
    @28
    wf
    #
    cA
    cA
    @32
    wf
    #
    @89
    @85
    wb
    @22
    @95
    @2
    @83
    cA
    cB
    @21
    f1of1
    ad2antlr
    @88
    @35
    @96
    @27
    @35
    @38
    @82
    simprll
    cA
    cA
    @28
    f1of
    syl
    @88
    @78
    @97
    @94
    cA
    cA
    @32
    f1of
    syl
    cA
    cA
    cB
    @21
    @28
    @32
    cocan1
    syl3anc
    bitrd
    ex
    syl5bi
    dom2d
    ex
    exlimdv
    mp2d
    @2
    @10
    cfn
    wcel
    #
    @24
    @19
    @20
    wb
    @2
    cA
    cfn
    wcel
    #
    @98
    @1
    @0
    @99
    cA
    cB
    enfii
    ancoms
    #
    @8
    cA
    vf
    deranglem
    syl
    @25
    @10
    @15
    cfn
    hashdom
    syl2anc
    mpbird
    @2
    @99
    @17
    @11
    wceq
    @100
    vx
    vy
    cA
    cD
    vf
    derang.d
    derangval
    syl
    @1
    @18
    @16
    wceq
    @0
    vx
    vy
    cB
    cD
    vf
    derang.d
    derangval
    adantl
    3brtr4d
end
