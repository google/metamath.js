include "wcel.mm"
include "ctop.mm"
include "wf.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cima.mm"
include "crn.mm"
include "cres.mm"
include "df-ima.mm"
include "wss.mm"
include "cuni.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "adantl.mm"
include "resmptd.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "wel.mm"
include "wrex.mm"
include "wral.mm"
include "wfn.mm"
include "wceq.mm"
include "cdif.mm"
include "cfn.mm"
include "cixp.mm"
include "wex.mm"
include "cab.mm"
include "ctg.mm"
include "cpt.mm"
include "ffn.mm"
include "eqid.mm"
include "ptval.mm"
include "sylan2.mm"
include "3adant3.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "tg2.mm"
include "sylan.mm"
include "wi.mm"
include "vex.mm"
include "weq.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "elab.mm"
include "simpl3.mm"
include "ad3antrrr.mm"
include "simplr2.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "elixp.mm"
include "simprbi.mm"
include "ad2antrl.mm"
include "cif.mm"
include "simplrr.mm"
include "simplrl.mm"
include "eleqtrrd.mm"
include "wn.mm"
include "simprr.mm"
include "syl.mm"
include "adantr.mm"
include "ifclda.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "wb.mm"
include "simpll1.mm"
include "mptelixpg.mm"
include "mpbird.mm"
include "cbvixpv.mm"
include "syl6eleq.mm"
include "sseldd.mm"
include "iftrue.mm"
include "fvmpt.mm"
include "eqcomd.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "cvv.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "syl12anc.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "fvex.mm"
include "rgenw.mm"
include "cbvmptv.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "ralrnmpt.mm"
include "simpl2.mm"
include "ffvelrnd.mm"
include "eltop2.mm"
include "eqeltrd.mm"

theorem ptpjopn
  let vx: setvar x
  let cA: class A
  let cU: class U
  let cF: class F
  let cI: class I
  let cJ: class J
  let cV: class V
  let cY: class Y
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume ptpjcn.1: |- Y = U. J
  assume ptpjcn.2: |- J = ( Xt_ ` F )

  disjoint A x
  disjoint F x
  disjoint I x
  disjoint V x
  disjoint Y x
  disjoint U x
  disjoint g k
  disjoint g n
  disjoint g s
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k n
  disjoint k s
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n s
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F g
  disjoint F k
  disjoint F n
  disjoint F s
  disjoint F u
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint J g
  disjoint J k
  disjoint J n
  disjoint J s
  disjoint J u
  disjoint J w
  disjoint I g
  disjoint I k
  disjoint I n
  disjoint I s
  disjoint I u
  disjoint I w
  disjoint I y
  disjoint I z
  disjoint V g
  disjoint V k
  disjoint V n
  disjoint V s
  disjoint V u
  disjoint V w
  disjoint V y
  disjoint V z
  disjoint Y u
  disjoint U g
  disjoint U k
  disjoint U n
  disjoint U s
  disjoint U w
  disjoint U y
  disjoint U z
  assert |- ( ( ( A e. V /\ F : A --> Top /\ I e. A ) /\ U e. J ) -> ( ( x e. Y |-> ( x ` I ) ) " U ) e. ( F ` I ) )

  proof
    cA
    cV
    wcel
    #
    cA
    ctop
    cF
    wf
    #
    cI
    cA
    wcel
    #
    w3a
    #
    cU
    cJ
    wcel
    #
    wa
    #
    vx
    cY
    cI
    vx
    cv
    #
    cfv
    #
    cmpt
    #
    cU
    cima
    #
    vx
    cU
    @7
    cmpt
    #
    crn
    #
    cI
    cF
    cfv
    #
    @5
    @9
    @8
    cU
    cres
    #
    crn
    @11
    @8
    cU
    df-ima
    @5
    @13
    @10
    @5
    vx
    cY
    cU
    @7
    @4
    cU
    cY
    wss
    @3
    @4
    cU
    cJ
    cuni
    cY
    cU
    cJ
    elssuni
    ptpjcn.1
    syl6sseqr
    adantl
    resmptd
    rneqd
    syl5eq
    @5
    @11
    @12
    wcel
    #
    vy
    vz
    wel
    #
    vz
    cv
    #
    @11
    wss
    #
    wa
    #
    vz
    @12
    wrex
    #
    vy
    @11
    wral
    #
    @5
    cI
    vs
    cv
    #
    cfv
    #
    @16
    wcel
    #
    @17
    wa
    #
    vz
    @12
    wrex
    #
    vs
    cU
    wral
    #
    @20
    @5
    @25
    vs
    cU
    @5
    @21
    cU
    wcel
    #
    wa
    #
    vs
    vw
    wel
    #
    vw
    cv
    #
    cU
    wss
    #
    wa
    #
    vw
    vg
    cv
    #
    cA
    wfn
    #
    vy
    cv
    #
    @33
    cfv
    #
    @35
    cF
    cfv
    #
    wcel
    #
    vy
    cA
    wral
    #
    @36
    @37
    cuni
    wceq
    vy
    cA
    @16
    cdif
    wral
    vz
    cfn
    wrex
    #
    w3a
    #
    @21
    vy
    cA
    @36
    cixp
    #
    wceq
    #
    wa
    #
    vg
    wex
    #
    vs
    cab
    #
    wrex
    #
    @25
    @5
    cU
    @46
    ctg
    cfv
    #
    wcel
    #
    @27
    @47
    @3
    @4
    @49
    @3
    cJ
    @48
    cU
    @0
    @1
    cJ
    @48
    wceq
    @2
    @0
    @1
    wa
    cJ
    cF
    cpt
    cfv
    #
    @48
    ptpjcn.2
    @1
    @0
    cF
    cA
    wfn
    @50
    @48
    wceq
    cA
    ctop
    cF
    ffn
    vs
    vy
    vz
    cA
    @46
    vg
    cF
    cV
    @46
    eqid
    ptval
    sylan2
    syl5eq
    3adant3
    eleq2d
    biimpa
    vw
    cU
    @46
    @21
    tg2
    sylan
    @28
    @32
    @25
    vw
    @46
    @30
    @46
    wcel
    @41
    @30
    @42
    wceq
    #
    wa
    #
    vg
    wex
    #
    @28
    @32
    @25
    wi
    #
    @45
    @53
    vs
    @30
    vw
    vex
    vs
    vw
    weq
    #
    @44
    @52
    vg
    @55
    @43
    @51
    @41
    @21
    @30
    @42
    eqeq1
    anbi2d
    exbidv
    elab
    @28
    @52
    @54
    vg
    @28
    @41
    @51
    @54
    @28
    @41
    wa
    #
    @54
    @51
    @21
    @42
    wcel
    #
    @42
    cU
    wss
    #
    wa
    #
    @25
    wi
    @56
    @59
    @25
    @56
    @59
    wa
    #
    cI
    @33
    cfv
    #
    @12
    wcel
    #
    @22
    @61
    wcel
    #
    @61
    @11
    wss
    #
    @25
    @60
    @2
    @39
    @62
    @5
    @2
    @27
    @41
    @59
    @0
    @1
    @2
    @4
    simpl3
    #
    ad3antrrr
    #
    @34
    @39
    @40
    @28
    @59
    simplr2
    @38
    @62
    vy
    cI
    cA
    @35
    cI
    wceq
    #
    @36
    @61
    @37
    @12
    @35
    cI
    @33
    fveq2
    #
    @35
    cI
    cF
    fveq2
    eleq12d
    rspcv
    sylc
    @60
    @2
    @35
    @21
    cfv
    #
    @36
    wcel
    #
    vy
    cA
    wral
    #
    @63
    @66
    @57
    @71
    @56
    @58
    @57
    @21
    cA
    wfn
    @71
    vy
    cA
    @36
    @21
    vs
    vex
    elixp
    simprbi
    #
    ad2antrl
    @70
    @63
    vy
    cI
    cA
    @67
    @69
    @22
    @36
    @61
    @35
    cI
    @21
    fveq2
    @68
    eleq12d
    rspcv
    sylc
    @60
    vk
    @61
    @11
    @60
    vk
    cv
    #
    @61
    wcel
    #
    @73
    @11
    wcel
    #
    @60
    @74
    wa
    #
    @73
    @7
    wceq
    #
    vx
    cU
    wrex
    #
    @75
    @76
    vn
    cA
    vn
    cv
    #
    cI
    wceq
    #
    @73
    @79
    @21
    cfv
    #
    cif
    #
    cmpt
    #
    cU
    wcel
    @73
    cI
    @83
    cfv
    #
    wceq
    #
    @78
    @76
    @42
    cU
    @83
    @56
    @57
    @58
    @74
    simplrr
    @76
    @83
    vn
    cA
    @79
    @33
    cfv
    #
    cixp
    #
    @42
    @76
    @83
    @87
    wcel
    #
    @82
    @86
    wcel
    #
    vn
    cA
    wral
    #
    @76
    @89
    vn
    cA
    @60
    @74
    @79
    cA
    wcel
    #
    @89
    @60
    @74
    @91
    wa
    #
    wa
    #
    @80
    @73
    @81
    @86
    @93
    @80
    wa
    @73
    @61
    @86
    @60
    @74
    @91
    @80
    simplrl
    @80
    @86
    @61
    wceq
    @93
    @79
    cI
    @33
    fveq2
    adantl
    eleqtrrd
    @93
    @81
    @86
    wcel
    #
    @80
    wn
    @93
    @91
    @71
    @94
    @60
    @74
    @91
    simprr
    @93
    @57
    @71
    @56
    @57
    @58
    @92
    simplrl
    @72
    syl
    @70
    @94
    vy
    @79
    cA
    vy
    vn
    weq
    @69
    @81
    @36
    @86
    @35
    @79
    @21
    fveq2
    @35
    @79
    @33
    fveq2
    eleq12d
    rspcv
    sylc
    adantr
    ifclda
    anassrs
    ralrimiva
    @76
    @0
    @88
    @90
    wb
    @28
    @0
    @41
    @59
    @74
    @0
    @1
    @2
    @4
    @27
    simpll1
    ad3antrrr
    vn
    cA
    @82
    @86
    cV
    mptelixpg
    syl
    mpbird
    vn
    vy
    cA
    @86
    @36
    @79
    @35
    @33
    fveq2
    cbvixpv
    syl6eleq
    sseldd
    @76
    @84
    @73
    @76
    @2
    @84
    @73
    wceq
    @60
    @2
    @74
    @66
    adantr
    vn
    cI
    @82
    @73
    cA
    @83
    @80
    @73
    @81
    iftrue
    @83
    eqid
    vk
    vex
    #
    fvmpt
    syl
    eqcomd
    @77
    @85
    vx
    @83
    cU
    @6
    @83
    wceq
    @7
    @84
    @73
    cI
    @6
    @83
    fveq1
    eqeq2d
    rspcev
    syl2anc
    @73
    cvv
    wcel
    @75
    @78
    wb
    @95
    vx
    cU
    @7
    @73
    @10
    cvv
    @10
    eqid
    elrnmpt
    ax-mp
    sylibr
    ex
    ssrdv
    @24
    @63
    @64
    wa
    vz
    @61
    @12
    @16
    @61
    wceq
    @23
    @63
    @17
    @64
    @16
    @61
    @22
    eleq2
    @16
    @61
    @11
    sseq1
    anbi12d
    rspcev
    syl12anc
    ex
    @51
    @32
    @59
    @25
    @51
    @29
    @57
    @31
    @58
    @30
    @42
    @21
    eleq2
    @30
    @42
    cU
    sseq1
    anbi12d
    imbi1d
    syl5ibrcom
    expimpd
    exlimdv
    syl5bi
    rexlimdv
    mpd
    ralrimiva
    @22
    cvv
    wcel
    #
    vs
    cU
    wral
    @20
    @26
    wb
    @96
    vs
    cU
    cI
    @21
    fvex
    rgenw
    @19
    @25
    vs
    vy
    cU
    @22
    @10
    cvv
    vx
    vs
    cU
    @7
    @22
    cI
    @6
    @21
    fveq1
    cbvmptv
    @35
    @22
    wceq
    #
    @18
    @24
    vz
    @12
    @97
    @15
    @23
    @17
    @35
    @22
    @16
    eleq1
    anbi1d
    rexbidv
    ralrnmpt
    ax-mp
    sylibr
    @5
    @12
    ctop
    wcel
    @14
    @20
    wb
    @5
    cA
    ctop
    cI
    cF
    @0
    @1
    @2
    @4
    simpl2
    @65
    ffvelrnd
    vy
    vz
    @11
    @12
    eltop2
    syl
    mpbird
    eqeltrd
end
