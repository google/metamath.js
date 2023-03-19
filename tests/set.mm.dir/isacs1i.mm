include "wcel.mm"
include "cpw.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "cfn.mm"
include "cin.mm"
include "cima.mm"
include "cuni.mm"
include "wss.mm"
include "crab.mm"
include "cmre.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wex.mm"
include "cacs.mm"
include "ssrab2.mm"
include "a1i.mm"
include "cint.mm"
include "inss1.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "ad2antrr.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "adantl.mm"
include "syl5ss.mm"
include "unissd.mm"
include "unipw.mm"
include "syl6sseq.mm"
include "adantr.mm"
include "wel.mm"
include "inss2.mm"
include "intss1.mm"
include "sspwb.mm"
include "sylib.mm"
include "ssrin.mm"
include "syl.mm"
include "imass2.mm"
include "ssel2.mm"
include "weq.mm"
include "pweq.mm"
include "ineq1d.mm"
include "imaeq2d.mm"
include "unieqd.mm"
include "id.mm"
include "sseq12d.mm"
include "elrab.mm"
include "simprbi.mm"
include "adantll.mm"
include "sstrd.mm"
include "ralrimiva.mm"
include "ssint.mm"
include "sylibr.mm"
include "ssind.mm"
include "wceq.mm"
include "sylanbrc.mm"
include "ismred2.mm"
include "cvv.mm"
include "cxp.mm"
include "fssxp.mm"
include "pwexg.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "ssexg.mm"
include "syl2anr.mm"
include "simpr.mm"
include "elrab3.mm"
include "rgen.mm"
include "jctir.mm"
include "feq1.mm"
include "imaeq1.mm"
include "sseq1d.mm"
include "bibi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "isacs.mm"

theorem isacs1i
  let cF: class F
  let cV: class V
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vt: setvar t
  let vf: setvar f

  disjoint F s
  disjoint X s
  disjoint F a
  disjoint F t
  disjoint a s
  disjoint a t
  disjoint s t
  disjoint F f
  disjoint V a
  disjoint V t
  disjoint X a
  disjoint X t
  disjoint X f
  disjoint f s
  disjoint f t
  assert |- ( ( X e. V /\ F : ~P X --> ~P X ) -> { s e. ~P X | U. ( F " ( ~P s i^i Fin ) ) C_ s } e. ( ACS ` X ) )

  proof
    cX
    cV
    wcel
    #
    cX
    cpw
    #
    @1
    cF
    wf
    #
    wa
    #
    cF
    vs
    cv
    #
    cpw
    #
    cfn
    cin
    #
    cima
    #
    cuni
    #
    @4
    wss
    #
    vs
    @1
    crab
    #
    cX
    cmre
    cfv
    wcel
    @1
    @1
    vf
    cv
    #
    wf
    #
    vt
    cv
    #
    @10
    wcel
    #
    @11
    @13
    cpw
    #
    cfn
    cin
    #
    cima
    #
    cuni
    #
    @13
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
    @10
    cX
    cacs
    cfv
    wcel
    @3
    @10
    cX
    vt
    @10
    @1
    wss
    @3
    @9
    vs
    @1
    ssrab2
    a1i
    @3
    @13
    @10
    wss
    #
    wa
    #
    cX
    @13
    cint
    #
    cin
    #
    @1
    wcel
    #
    cF
    @27
    cpw
    #
    cfn
    cin
    #
    cima
    #
    cuni
    #
    @27
    wss
    #
    @27
    @10
    wcel
    @0
    @28
    @2
    @24
    @0
    @28
    @27
    cX
    wss
    cX
    @26
    inss1
    @27
    cX
    cV
    elpw2g
    mpbiri
    ad2antrr
    @25
    @32
    cX
    @26
    @3
    @32
    cX
    wss
    @24
    @3
    @32
    @1
    cuni
    cX
    @3
    @31
    @1
    @3
    @31
    cF
    crn
    #
    @1
    cF
    @30
    imassrn
    @2
    @34
    @1
    wss
    @0
    @1
    @1
    cF
    frn
    adantl
    syl5ss
    unissd
    cX
    unipw
    syl6sseq
    adantr
    @25
    @32
    va
    cv
    #
    wss
    #
    va
    @13
    wral
    @32
    @26
    wss
    @25
    @36
    va
    @13
    @25
    va
    vt
    wel
    #
    wa
    #
    @32
    cF
    @35
    cpw
    #
    cfn
    cin
    #
    cima
    #
    cuni
    #
    @35
    @38
    @31
    @41
    @38
    @30
    @40
    wss
    #
    @31
    @41
    wss
    @38
    @29
    @39
    wss
    #
    @43
    @38
    @27
    @35
    wss
    #
    @44
    @37
    @45
    @25
    @37
    @27
    @26
    @35
    cX
    @26
    inss2
    @35
    @13
    intss1
    syl5ss
    adantl
    @27
    @35
    sspwb
    sylib
    @29
    @39
    cfn
    ssrin
    syl
    @30
    @40
    cF
    imass2
    syl
    unissd
    @24
    @37
    @42
    @35
    wss
    #
    @3
    @24
    @37
    wa
    @35
    @10
    wcel
    #
    @46
    @13
    @10
    @35
    ssel2
    @47
    @35
    @1
    wcel
    @46
    @9
    @46
    vs
    @35
    @1
    vs
    va
    weq
    #
    @8
    @42
    @4
    @35
    @48
    @7
    @41
    @48
    @6
    @40
    cF
    @48
    @5
    @39
    cfn
    @4
    @35
    pweq
    ineq1d
    imaeq2d
    unieqd
    @48
    id
    sseq12d
    elrab
    simprbi
    syl
    adantll
    sstrd
    ralrimiva
    va
    @32
    @13
    ssint
    sylibr
    ssind
    @9
    @33
    vs
    @27
    @1
    @4
    @27
    wceq
    #
    @8
    @32
    @4
    @27
    @49
    @7
    @31
    @49
    @6
    @30
    cF
    @49
    @5
    @29
    cfn
    @4
    @27
    pweq
    ineq1d
    imaeq2d
    unieqd
    @49
    id
    sseq12d
    elrab
    sylanbrc
    ismred2
    @3
    cF
    cvv
    wcel
    #
    @2
    @14
    cF
    @16
    cima
    #
    cuni
    #
    @13
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
    @23
    @2
    cF
    @1
    @1
    cxp
    #
    wss
    @57
    cvv
    wcel
    #
    @50
    @0
    @1
    @1
    cF
    fssxp
    @0
    @1
    cvv
    wcel
    #
    @59
    @58
    cX
    cV
    pwexg
    #
    @60
    @1
    @1
    cvv
    cvv
    xpexg
    syl2anc
    cF
    @57
    cvv
    ssexg
    syl2anr
    @3
    @2
    @55
    @0
    @2
    simpr
    @54
    vt
    @1
    @9
    @53
    vs
    @13
    @1
    vs
    vt
    weq
    #
    @8
    @52
    @4
    @13
    @61
    @7
    @51
    @61
    @6
    @16
    cF
    @61
    @5
    @15
    cfn
    @4
    @13
    pweq
    ineq1d
    imaeq2d
    unieqd
    @61
    id
    sseq12d
    elrab3
    rgen
    jctir
    @22
    @56
    vf
    cF
    cvv
    @11
    cF
    wceq
    #
    @12
    @2
    @21
    @55
    @1
    @1
    @11
    cF
    feq1
    @62
    @20
    @54
    vt
    @1
    @62
    @19
    @53
    @14
    @62
    @18
    @52
    @13
    @62
    @17
    @51
    @11
    cF
    @16
    imaeq1
    unieqd
    sseq1d
    bibi2d
    ralbidv
    anbi12d
    spcegv
    sylc
    @10
    vf
    cX
    vt
    isacs
    sylanbrc
end
