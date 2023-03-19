include "cv.mm"
include "cres.mm"
include "wceq.mm"
include "csn.mm"
include "cun.mm"
include "wf1.mm"
include "wa.mm"
include "cab.mm"
include "crn.mm"
include "cdif.mm"
include "cfv.mm"
include "cop.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wf.mm"
include "f1f.mm"
include "adantl.mm"
include "cfn.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "elmapd.mm"
include "syl5ibr.mm"
include "abssdv.mm"
include "ovex.mm"
include "ssexg.mm"
include "difexg.mm"
include "syl.mm"
include "vex.mm"
include "weq.mm"
include "reseq1.mm"
include "eqeq1d.mm"
include "f1eq1.mm"
include "anbi12d.mm"
include "elab.mm"
include "ad2antll.mm"
include "ssun2.mm"
include "snss.mm"
include "mpbir.mm"
include "ffvelrn.mm"
include "wn.mm"
include "adantr.mm"
include "cima.mm"
include "df-ima.mm"
include "simprl.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "wb.mm"
include "simprr.mm"
include "a1i.mm"
include "ssun1.mm"
include "f1elima.mm"
include "syl3anc.mm"
include "bitr3d.mm"
include "mtbird.mm"
include "eldifd.mm"
include "ex.mm"
include "syl5bi.mm"
include "cin.mm"
include "wf1o.mm"
include "f1osn.mm"
include "f1of.mm"
include "ax-mp.mm"
include "eldifi.mm"
include "snssd.mm"
include "fss.mm"
include "sylancr.mm"
include "c0.mm"
include "res0.mm"
include "eqtr4i.mm"
include "disjsn.mm"
include "sylibr.mm"
include "reseq2d.mm"
include "3eqtr4a.mm"
include "fresaunres1.mm"
include "f1f1orn.mm"
include "eldifn.mm"
include "f1oun.mm"
include "syl22anc.mm"
include "f1of1.mm"
include "frn.mm"
include "unssd.mm"
include "f1ss.mm"
include "syl2anc.mm"
include "fex.mm"
include "snex.mm"
include "unexg.mm"
include "elabg.mm"
include "mpbir2and.mm"
include "anbi1i.mm"
include "wral.mm"
include "wfn.mm"
include "simprlr.mm"
include "f1fn.mm"
include "adantrl.mm"
include "f1ofn.mm"
include "eqfnfv.mm"
include "fvres.mm"
include "eqcomd.mm"
include "simprll.mm"
include "fveq1d.mm"
include "sylan9eqr.mm"
include "ad2antrr.mm"
include "fnsn.mm"
include "simpr.mm"
include "fvun1.mm"
include "syl112anc.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "biantrurd.mm"
include "ralunb.mm"
include "syl6bbr.mm"
include "cdm.mm"
include "fdm.mm"
include "fsnunfv.mm"
include "eqeq2d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "ralsn.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "3bitr2d.mm"
include "en3d.mm"

theorem hashf1lem1
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cF: class F
  let va: setvar a
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume hashf1lem2.1: |- ( ph -> A e. Fin )
  assume hashf1lem2.2: |- ( ph -> B e. Fin )
  assume hashf1lem2.3: |- ( ph -> -. z e. A )
  assume hashf1lem2.4: |- ( ph -> ( ( # ` A ) + 1 ) <_ ( # ` B ) )
  assume hashf1lem1.5: |- ( ph -> F : A -1-1-> B )

  disjoint f z
  disjoint A f
  disjoint B f
  disjoint f ph
  disjoint F f
  disjoint a f
  disjoint a g
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A a
  disjoint A g
  disjoint A x
  disjoint A y
  disjoint B a
  disjoint B g
  disjoint B x
  disjoint B y
  disjoint a ph
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint F g
  disjoint F x
  disjoint F y
  assert |- ( ph -> { f | ( ( f |` A ) = F /\ f : ( A u. { z } ) -1-1-> B ) } ~~ ( B \ ran F ) )

  proof
    wph
    vg
    vx
    vf
    cv
    #
    cA
    cres
    #
    cF
    wceq
    #
    cA
    vz
    cv
    #
    csn
    #
    cun
    #
    cB
    @0
    wf1
    #
    wa
    #
    vf
    cab
    #
    cB
    cF
    crn
    #
    cdif
    #
    @3
    vg
    cv
    #
    cfv
    #
    cF
    @3
    vx
    cv
    #
    cop
    #
    csn
    #
    cun
    #
    wph
    @8
    cB
    @5
    cmap
    co
    #
    wss
    @17
    cvv
    wcel
    @8
    cvv
    wcel
    wph
    @7
    vf
    @17
    @7
    @0
    @17
    wcel
    wph
    @5
    cB
    @0
    wf
    #
    @6
    @18
    @2
    @5
    cB
    @0
    f1f
    adantl
    wph
    cB
    @5
    @0
    cfn
    cfn
    hashf1lem2.2
    wph
    cA
    cfn
    wcel
    #
    @4
    cfn
    wcel
    @5
    cfn
    wcel
    hashf1lem2.1
    @3
    snfi
    cA
    @4
    unfi
    sylancl
    elmapd
    syl5ibr
    abssdv
    cB
    @5
    cmap
    ovex
    @8
    @17
    cvv
    ssexg
    sylancl
    wph
    cB
    cfn
    wcel
    @10
    cvv
    wcel
    hashf1lem2.2
    cB
    @9
    cfn
    difexg
    syl
    @11
    @8
    wcel
    #
    @11
    cA
    cres
    #
    cF
    wceq
    #
    @5
    cB
    @11
    wf1
    #
    wa
    #
    wph
    @12
    @10
    wcel
    #
    @7
    @24
    vf
    @11
    vg
    vex
    vf
    vg
    weq
    #
    @2
    @22
    @6
    @23
    @26
    @1
    @21
    cF
    @0
    @11
    cA
    reseq1
    eqeq1d
    @5
    cB
    @0
    @11
    f1eq1
    anbi12d
    elab
    #
    wph
    @24
    @25
    wph
    @24
    wa
    #
    @12
    cB
    @9
    @28
    @5
    cB
    @11
    wf
    #
    @3
    @5
    wcel
    #
    @12
    cB
    wcel
    @23
    @29
    wph
    @22
    @5
    cB
    @11
    f1f
    ad2antll
    @30
    @4
    @5
    wss
    @4
    cA
    ssun2
    @3
    @5
    vz
    vex
    #
    snss
    mpbir
    #
    @5
    cB
    @3
    @11
    ffvelrn
    sylancl
    @28
    @12
    @9
    wcel
    #
    @3
    cA
    wcel
    #
    wph
    @34
    wn
    #
    @24
    hashf1lem2.3
    adantr
    @28
    @12
    @11
    cA
    cima
    #
    wcel
    #
    @33
    @34
    @28
    @36
    @9
    @12
    @28
    @36
    @21
    crn
    @9
    @11
    cA
    df-ima
    @28
    @21
    cF
    wph
    @22
    @23
    simprl
    rneqd
    syl5eq
    eleq2d
    @28
    @23
    @30
    cA
    @5
    wss
    #
    @37
    @34
    wb
    wph
    @22
    @23
    simprr
    @30
    @28
    @32
    a1i
    @38
    @28
    cA
    @4
    ssun1
    a1i
    @5
    cB
    @11
    @3
    cA
    f1elima
    syl3anc
    bitr3d
    mtbird
    eldifd
    ex
    syl5bi
    wph
    @13
    @10
    wcel
    #
    @16
    @8
    wcel
    #
    wph
    @39
    wa
    #
    @40
    @16
    cA
    cres
    #
    cF
    wceq
    #
    @5
    cB
    @16
    wf1
    #
    @41
    cA
    cB
    cF
    wf
    #
    @4
    cB
    @15
    wf
    #
    cF
    cA
    @4
    cin
    #
    cres
    #
    @15
    @47
    cres
    #
    wceq
    @43
    wph
    @45
    @39
    wph
    cA
    cB
    cF
    wf1
    #
    @45
    hashf1lem1.5
    cA
    cB
    cF
    f1f
    syl
    #
    adantr
    #
    @41
    @4
    @13
    csn
    #
    @15
    wf
    #
    @53
    cB
    wss
    @46
    @4
    @53
    @15
    wf1o
    #
    @54
    @3
    @13
    @31
    vx
    vex
    #
    f1osn
    #
    @4
    @53
    @15
    f1of
    ax-mp
    @41
    @13
    cB
    @39
    @13
    cB
    wcel
    wph
    @13
    cB
    @9
    eldifi
    adantl
    snssd
    #
    @4
    @53
    cB
    @15
    fss
    sylancr
    @41
    cF
    c0
    cres
    #
    @15
    c0
    cres
    #
    @48
    @49
    @59
    c0
    @60
    cF
    res0
    @15
    res0
    eqtr4i
    @41
    @47
    c0
    cF
    wph
    @47
    c0
    wceq
    #
    @39
    wph
    @35
    @61
    hashf1lem2.3
    cA
    @3
    disjsn
    sylibr
    #
    adantr
    #
    reseq2d
    @41
    @47
    c0
    @15
    @63
    reseq2d
    3eqtr4a
    cA
    @4
    cB
    cF
    @15
    fresaunres1
    syl3anc
    @41
    @5
    @9
    @53
    cun
    #
    @16
    wf1
    #
    @64
    cB
    wss
    @44
    @41
    @5
    @64
    @16
    wf1o
    #
    @65
    @41
    cA
    @9
    cF
    wf1o
    #
    @55
    @61
    @9
    @53
    cin
    c0
    wceq
    #
    @66
    wph
    @67
    @39
    wph
    @50
    @67
    hashf1lem1.5
    cA
    cB
    cF
    f1f1orn
    syl
    adantr
    @55
    @41
    @57
    a1i
    @63
    @41
    @13
    @9
    wcel
    wn
    #
    @68
    @39
    @69
    wph
    @13
    cB
    @9
    eldifn
    adantl
    @9
    @13
    disjsn
    sylibr
    cA
    @9
    @4
    @53
    cF
    @15
    f1oun
    syl22anc
    #
    @5
    @64
    @16
    f1of1
    syl
    @41
    @9
    @53
    cB
    @41
    @45
    @9
    cB
    wss
    @52
    cA
    cB
    cF
    frn
    syl
    @58
    unssd
    @5
    @64
    cB
    @16
    f1ss
    syl2anc
    @41
    @16
    cvv
    wcel
    #
    @40
    @43
    @44
    wa
    #
    wb
    @41
    cF
    cvv
    wcel
    #
    @15
    cvv
    wcel
    @71
    wph
    @73
    @39
    wph
    @45
    @19
    @73
    @51
    hashf1lem2.1
    cA
    cB
    cfn
    cF
    fex
    syl2anc
    adantr
    @14
    snex
    cF
    @15
    cvv
    cvv
    unexg
    sylancl
    @7
    @72
    vf
    @16
    cvv
    @0
    @16
    wceq
    #
    @2
    @43
    @6
    @44
    @74
    @1
    @42
    cF
    @0
    @16
    cA
    reseq1
    eqeq1d
    @5
    cB
    @0
    @16
    f1eq1
    anbi12d
    elabg
    syl
    mpbir2and
    ex
    @20
    @39
    wa
    @24
    @39
    wa
    #
    wph
    @11
    @16
    wceq
    #
    @13
    @12
    wceq
    #
    wb
    #
    @20
    @24
    @39
    @27
    anbi1i
    wph
    @75
    @78
    wph
    @75
    wa
    #
    @76
    vy
    cv
    #
    @11
    cfv
    #
    @80
    @16
    cfv
    #
    wceq
    #
    vy
    @5
    wral
    #
    @83
    vy
    @4
    wral
    #
    @77
    @79
    @11
    @5
    wfn
    #
    @16
    @5
    wfn
    #
    @76
    @84
    wb
    @79
    @23
    @86
    wph
    @22
    @23
    @39
    simprlr
    @5
    cB
    @11
    f1fn
    syl
    @79
    @66
    @87
    wph
    @39
    @66
    @24
    @70
    adantrl
    @5
    @64
    @16
    f1ofn
    syl
    vy
    @5
    @11
    @16
    eqfnfv
    syl2anc
    @79
    @85
    @83
    vy
    cA
    wral
    #
    @85
    wa
    @84
    @79
    @88
    @85
    @79
    @83
    vy
    cA
    @79
    @80
    cA
    wcel
    #
    wa
    #
    @81
    @80
    cF
    cfv
    #
    @82
    @89
    @79
    @81
    @80
    @21
    cfv
    #
    @91
    @89
    @92
    @81
    @80
    cA
    @11
    fvres
    eqcomd
    @79
    @80
    @21
    cF
    wph
    @22
    @23
    @39
    simprll
    fveq1d
    sylan9eqr
    @90
    cF
    cA
    wfn
    #
    @15
    @4
    wfn
    #
    @61
    @89
    @82
    @91
    wceq
    @90
    @50
    @93
    wph
    @50
    @75
    @89
    hashf1lem1.5
    ad2antrr
    cA
    cB
    cF
    f1fn
    syl
    @94
    @90
    @3
    @13
    @31
    @56
    fnsn
    a1i
    wph
    @61
    @75
    @89
    @62
    ad2antrr
    @79
    @89
    simpr
    cA
    @4
    cF
    @15
    @80
    fvun1
    syl112anc
    eqtr4d
    ralrimiva
    biantrurd
    @83
    vy
    cA
    @4
    ralunb
    syl6bbr
    @79
    @12
    @3
    @16
    cfv
    #
    wceq
    #
    @12
    @13
    wceq
    @85
    @77
    @79
    @95
    @13
    @12
    @79
    @3
    cvv
    wcel
    #
    @13
    cvv
    wcel
    #
    @3
    cF
    cdm
    #
    wcel
    #
    wn
    #
    @95
    @13
    wceq
    @97
    @79
    @31
    a1i
    @98
    @79
    @56
    a1i
    wph
    @101
    @75
    wph
    @100
    @34
    hashf1lem2.3
    wph
    @99
    cA
    @3
    wph
    @45
    @99
    cA
    wceq
    @51
    cA
    cB
    cF
    fdm
    syl
    eleq2d
    mtbird
    adantr
    cF
    cvv
    cvv
    @3
    @13
    fsnunfv
    syl3anc
    eqeq2d
    @83
    @96
    vy
    @3
    @31
    vy
    vz
    weq
    @81
    @12
    @82
    @95
    @80
    @3
    @11
    fveq2
    @80
    @3
    @16
    fveq2
    eqeq12d
    ralsn
    @13
    @12
    eqcom
    3bitr4g
    3bitr2d
    ex
    syl5bi
    en3d
end
