include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cmre.mm"
include "cpw.mm"
include "cv.mm"
include "wf.mm"
include "cfn.mm"
include "cin.mm"
include "cima.mm"
include "cuni.mm"
include "wss.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "isacs.mm"
include "ciun.mm"
include "iunss.mm"
include "wfun.mm"
include "wceq.mm"
include "ffun.mm"
include "funiunfv.mm"
include "syl.mm"
include "sseq1d.mm"
include "syl5rbbr.mm"
include "bibi2d.mm"
include "ralbidv.mm"
include "pm5.32i.mm"
include "exbii.mm"
include "simpll.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwi.mm"
include "adantl.mm"
include "simplr.mm"
include "mrcsscl.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "adantlr.mm"
include "adantllr.mm"
include "wi.mm"
include "simplll.mm"
include "ad2antlr.mm"
include "sstrd.mm"
include "mrcssidd.mm"
include "vex.mm"
include "elpw.mm"
include "sylibr.mm"
include "inss2.mm"
include "elind.mm"
include "mrccl.mm"
include "syl2anc.mm"
include "mresspw.mm"
include "ad3antrrr.mm"
include "sseldd.mm"
include "simprr.mm"
include "ad2antrr.mm"
include "eleq1.mm"
include "pweq.mm"
include "ineq1d.mm"
include "sseq2.mm"
include "raleqbidv.mm"
include "bibi12d.mm"
include "rspcva.mm"
include "mpbid.mm"
include "weq.mm"
include "fveq2.mm"
include "sstr2.mm"
include "ralimdva.mm"
include "imp.mm"
include "cbvralv.mm"
include "sylib.mm"
include "mpbird.mm"
include "impbida.mm"
include "ex.mm"
include "exlimdv.mm"
include "mrcf.mm"
include "fssd.mm"
include "cmrc.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "feq1.mm"
include "fveq1.mm"
include "syl6bb.mm"
include "anbi12d.mm"
include "spcev.mm"
include "sylan.mm"
include "impbid.mm"
include "syl5bb.mm"
include "bitri.mm"

theorem isacs2
  let vy: setvar y
  let cC: class C
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vc: setvar c
  let vf: setvar f
  let vt: setvar t
  let vz: setvar z
  let cS: class S
  let vx: setvar x
  assume isacs2.f: |- F = ( mrCls ` C )

  disjoint C s
  disjoint C y
  disjoint F s
  disjoint F y
  disjoint s y
  disjoint X s
  disjoint X y
  disjoint C c
  disjoint C f
  disjoint c f
  disjoint c s
  disjoint f s
  disjoint C t
  disjoint t y
  disjoint F f
  disjoint F t
  disjoint F z
  disjoint f t
  disjoint f y
  disjoint f z
  disjoint s t
  disjoint s z
  disjoint t z
  disjoint y z
  disjoint S s
  disjoint S y
  disjoint X c
  disjoint X f
  disjoint X x
  disjoint c x
  disjoint f x
  disjoint s x
  disjoint X t
  assert |- ( C e. ( ACS ` X ) <-> ( C e. ( Moore ` X ) /\ A. s e. ~P X ( s e. C <-> A. y e. ( ~P s i^i Fin ) ( F ` y ) C_ s ) ) )

  proof
    cC
    cX
    cacs
    cfv
    wcel
    cC
    cX
    cmre
    cfv
    wcel
    #
    cX
    cpw
    #
    @1
    vf
    cv
    #
    wf
    #
    vt
    cv
    #
    cC
    wcel
    #
    @2
    @4
    cpw
    #
    cfn
    cin
    #
    cima
    cuni
    #
    @4
    wss
    #
    wb
    #
    vt
    @1
    wral
    #
    wa
    #
    vf
    wex
    #
    wa
    @0
    vs
    cv
    #
    cC
    wcel
    #
    vy
    cv
    #
    cF
    cfv
    #
    @14
    wss
    #
    vy
    @14
    cpw
    #
    cfn
    cin
    #
    wral
    #
    wb
    #
    vs
    @1
    wral
    #
    wa
    cC
    vf
    cX
    vt
    isacs
    @0
    @13
    @23
    @13
    @3
    @5
    vz
    cv
    #
    @2
    cfv
    #
    @4
    wss
    #
    vz
    @7
    wral
    #
    wb
    #
    vt
    @1
    wral
    #
    wa
    #
    vf
    wex
    #
    @0
    @23
    @12
    @30
    vf
    @3
    @11
    @29
    @3
    @10
    @28
    vt
    @1
    @3
    @9
    @27
    @5
    @27
    vz
    @7
    @25
    ciun
    #
    @4
    wss
    @3
    @9
    vz
    @7
    @25
    @4
    iunss
    @3
    @32
    @8
    @4
    @3
    @2
    wfun
    @32
    @8
    wceq
    @1
    @1
    @2
    ffun
    vz
    @7
    @2
    funiunfv
    syl
    sseq1d
    syl5rbbr
    bibi2d
    ralbidv
    pm5.32i
    exbii
    @0
    @31
    @23
    @0
    @30
    @23
    vf
    @0
    @30
    @23
    @0
    @30
    wa
    #
    @22
    vs
    @1
    @33
    @14
    @1
    wcel
    #
    wa
    #
    @15
    @21
    @0
    @34
    @15
    @21
    @30
    @0
    @15
    @21
    @34
    @0
    @15
    wa
    #
    @18
    vy
    @20
    @36
    @16
    @20
    wcel
    #
    wa
    @0
    @16
    @14
    wss
    #
    @15
    @18
    @0
    @15
    @37
    simpll
    @37
    @38
    @36
    @37
    @16
    @19
    wcel
    @38
    @20
    @19
    @16
    @19
    cfn
    inss1
    sseli
    @16
    @14
    elpwi
    syl
    #
    adantl
    @0
    @15
    @37
    simplr
    cC
    @16
    cF
    @14
    cX
    isacs2.f
    mrcsscl
    syl3anc
    ralrimiva
    adantlr
    adantllr
    @35
    @21
    wa
    #
    @15
    @25
    @14
    wss
    #
    vz
    @20
    wral
    #
    @40
    @16
    @2
    cfv
    #
    @14
    wss
    #
    vy
    @20
    wral
    #
    @42
    @35
    @21
    @45
    @35
    @18
    @44
    vy
    @20
    @35
    @37
    wa
    #
    @43
    @17
    wss
    #
    @18
    @44
    wi
    @46
    @16
    @17
    cpw
    #
    cfn
    cin
    #
    wcel
    @25
    @17
    wss
    #
    vz
    @49
    wral
    #
    @47
    @46
    @48
    cfn
    @16
    @46
    @16
    @17
    wss
    @16
    @48
    wcel
    @46
    cC
    @16
    cF
    cX
    @0
    @30
    @34
    @37
    simplll
    #
    isacs2.f
    @46
    @16
    @14
    cX
    @37
    @38
    @35
    @39
    adantl
    @34
    @14
    cX
    wss
    @33
    @37
    @14
    cX
    elpwi
    ad2antlr
    sstrd
    #
    mrcssidd
    @16
    @17
    vy
    vex
    elpw
    sylibr
    @37
    @16
    cfn
    wcel
    @35
    @20
    cfn
    @16
    @19
    cfn
    inss2
    sseli
    adantl
    elind
    @46
    @17
    cC
    wcel
    #
    @51
    @46
    @0
    @16
    cX
    wss
    @54
    @52
    @53
    cC
    @16
    cF
    cX
    isacs2.f
    mrccl
    syl2anc
    #
    @46
    @17
    @1
    wcel
    @29
    @54
    @51
    wb
    #
    @46
    cC
    @1
    @17
    @0
    cC
    @1
    wss
    @30
    @34
    @37
    cC
    cX
    mresspw
    #
    ad3antrrr
    @55
    sseldd
    @33
    @29
    @34
    @37
    @0
    @3
    @29
    simprr
    #
    ad2antrr
    @28
    @56
    vt
    @17
    @1
    @4
    @17
    wceq
    #
    @5
    @54
    @27
    @51
    @4
    @17
    cC
    eleq1
    @59
    @26
    @50
    vz
    @7
    @49
    @59
    @6
    @48
    cfn
    @4
    @17
    pweq
    ineq1d
    @4
    @17
    @25
    sseq2
    raleqbidv
    bibi12d
    rspcva
    syl2anc
    mpbid
    @50
    @47
    vz
    @16
    @49
    vz
    vy
    weq
    #
    @25
    @43
    @17
    @24
    @16
    @2
    fveq2
    sseq1d
    rspcva
    syl2anc
    @43
    @17
    @14
    sstr2
    syl
    ralimdva
    imp
    @44
    @41
    vy
    vz
    @20
    vy
    vz
    weq
    @43
    @25
    @14
    @16
    @24
    @2
    fveq2
    sseq1d
    cbvralv
    sylib
    @40
    @34
    @29
    @15
    @42
    wb
    #
    @33
    @34
    @21
    simplr
    @33
    @29
    @34
    @21
    @58
    ad2antrr
    @28
    @61
    vt
    @14
    @1
    vt
    vs
    weq
    #
    @5
    @15
    @27
    @42
    @4
    @14
    cC
    eleq1
    #
    @62
    @26
    @41
    vz
    @7
    @20
    @62
    @6
    @19
    cfn
    @4
    @14
    pweq
    ineq1d
    #
    @4
    @14
    @25
    sseq2
    raleqbidv
    bibi12d
    rspcva
    syl2anc
    mpbird
    impbida
    ralrimiva
    ex
    exlimdv
    @0
    @23
    @31
    @0
    @1
    @1
    cF
    wf
    #
    @23
    @31
    @0
    @1
    cC
    @1
    cF
    cC
    cF
    cX
    isacs2.f
    mrcf
    @57
    fssd
    @30
    @65
    @23
    wa
    vf
    cF
    cF
    cC
    cmrc
    cfv
    cvv
    isacs2.f
    cC
    cmrc
    fvex
    eqeltri
    @2
    cF
    wceq
    #
    @3
    @65
    @29
    @23
    @1
    @1
    @2
    cF
    feq1
    @66
    @29
    @5
    @17
    @4
    wss
    #
    vy
    @7
    wral
    #
    wb
    #
    vt
    @1
    wral
    @23
    @66
    @28
    @69
    vt
    @1
    @66
    @27
    @68
    @5
    @66
    @27
    @24
    cF
    cfv
    #
    @4
    wss
    #
    vz
    @7
    wral
    @68
    @66
    @26
    @71
    vz
    @7
    @66
    @25
    @70
    @4
    @24
    @2
    cF
    fveq1
    sseq1d
    ralbidv
    @71
    @67
    vz
    vy
    @7
    @60
    @70
    @17
    @4
    @24
    @16
    cF
    fveq2
    sseq1d
    cbvralv
    syl6bb
    bibi2d
    ralbidv
    @69
    @22
    vt
    vs
    @1
    @62
    @5
    @15
    @68
    @21
    @63
    @62
    @67
    @18
    vy
    @7
    @20
    @64
    @4
    @14
    @17
    sseq2
    raleqbidv
    bibi12d
    cbvralv
    syl6bb
    anbi12d
    spcev
    sylan
    ex
    impbid
    syl5bb
    pm5.32i
    bitri
end
