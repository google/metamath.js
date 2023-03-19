include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wf.mm"
include "wral.mm"
include "w3a.mm"
include "cmpt.mm"
include "cvv.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "weu.mm"
include "mptexg.mm"
include "3ad2ant2.mm"
include "cixp.mm"
include "ffvelrn.mm"
include "expcom.mm"
include "ralimdv.mm"
include "impcom.mm"
include "3ad2antl3.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eleq12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "wb.mm"
include "simpl1.mm"
include "mptelixpg.mm"
include "syl.mm"
include "mpbird.mm"
include "cbvixpv.mm"
include "eqtri.mm"
include "syl6eleqr.mm"
include "eqid.mm"
include "fmptd.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "fvex.mm"
include "fvmpt3i.mm"
include "adantl.mm"
include "mpteq2dv.mm"
include "adantlr.mm"
include "eqidd.mm"
include "rgenw.mm"
include "ixpexg.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fveq1.mm"
include "fmptco.mm"
include "rsp.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "feqmptd.mm"
include "3eqtr4rd.mm"
include "ex.mm"
include "ralrimi.mm"
include "simprl.mm"
include "simplrr.mm"
include "coeq1d.mm"
include "eqeq12d.mm"
include "rspccva.mm"
include "sylan.mm"
include "fvco3.mm"
include "adantr.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "wfn.mm"
include "syl6eleq.mm"
include "ixpfn.mm"
include "dffn5.mm"
include "eqtr4d.mm"
include "alrimiv.mm"
include "feq1.mm"
include "coeq2.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "eqeu.mm"
include "syl121anc.mm"

theorem upixp
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let vh: setvar h
  let cF: class F
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vu: setvar u
  assume upixp.1: |- X = X_ b e. A ( C ` b )
  assume upixp.2: |- P = ( w e. A |-> ( x e. X |-> ( x ` w ) ) )

  disjoint A a
  disjoint A b
  disjoint A h
  disjoint A w
  disjoint A x
  disjoint a b
  disjoint a h
  disjoint a w
  disjoint a x
  disjoint b h
  disjoint b w
  disjoint b x
  disjoint h w
  disjoint h x
  disjoint w x
  disjoint R a
  disjoint R b
  disjoint R h
  disjoint R w
  disjoint R x
  disjoint S a
  disjoint S b
  disjoint S h
  disjoint S w
  disjoint S x
  disjoint F a
  disjoint F b
  disjoint F h
  disjoint F w
  disjoint F x
  disjoint B a
  disjoint B b
  disjoint B h
  disjoint B w
  disjoint B x
  disjoint C a
  disjoint C b
  disjoint C h
  disjoint C w
  disjoint C x
  disjoint X a
  disjoint X h
  disjoint X w
  disjoint X x
  disjoint P a
  disjoint P h
  disjoint A s
  disjoint A u
  disjoint a s
  disjoint a u
  disjoint b s
  disjoint b u
  disjoint h s
  disjoint h u
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint u w
  disjoint u x
  disjoint R s
  disjoint R u
  disjoint S s
  disjoint S u
  disjoint F s
  disjoint F u
  disjoint B s
  disjoint B u
  disjoint C s
  disjoint C u
  disjoint X s
  disjoint X u
  disjoint P s
  disjoint P u
  assert |- ( ( A e. R /\ B e. S /\ A. a e. A ( F ` a ) : B --> ( C ` a ) ) -> E! h ( h : B --> X /\ A. a e. A ( F ` a ) = ( ( P ` a ) o. h ) ) )

  proof
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    cB
    va
    cv
    #
    cC
    cfv
    #
    @2
    cF
    cfv
    #
    wf
    #
    va
    cA
    wral
    #
    w3a
    #
    vu
    cB
    vs
    cA
    vu
    cv
    #
    vs
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    cvv
    wcel
    #
    cB
    cX
    @13
    wf
    #
    @4
    @2
    cP
    cfv
    #
    @13
    ccom
    #
    wceq
    #
    va
    cA
    wral
    #
    cB
    cX
    vh
    cv
    #
    wf
    #
    @4
    @16
    @20
    ccom
    #
    wceq
    #
    va
    cA
    wral
    #
    wa
    #
    @20
    @13
    wceq
    #
    wi
    #
    vh
    wal
    @25
    vh
    weu
    @1
    @0
    @14
    @6
    vu
    cB
    @12
    cS
    mptexg
    3ad2ant2
    @7
    vu
    cB
    @12
    cX
    @13
    @7
    @8
    cB
    wcel
    #
    wa
    #
    @12
    vs
    cA
    @9
    cC
    cfv
    #
    cixp
    #
    cX
    @29
    @12
    @31
    wcel
    #
    @11
    @30
    wcel
    #
    vs
    cA
    wral
    #
    @29
    @8
    @4
    cfv
    #
    @3
    wcel
    #
    va
    cA
    wral
    #
    @34
    @6
    @0
    @28
    @37
    @1
    @28
    @6
    @37
    @28
    @5
    @36
    va
    cA
    @5
    @28
    @36
    cB
    @3
    @8
    @4
    ffvelrn
    expcom
    ralimdv
    impcom
    3ad2antl3
    @36
    @33
    va
    vs
    cA
    @2
    @9
    wceq
    #
    @35
    @11
    @3
    @30
    @38
    @8
    @4
    @10
    @2
    @9
    cF
    fveq2
    #
    fveq1d
    @2
    @9
    cC
    fveq2
    eleq12d
    cbvralv
    sylib
    @29
    @0
    @32
    @34
    wb
    @0
    @1
    @6
    @28
    simpl1
    vs
    cA
    @11
    @30
    cR
    mptelixpg
    syl
    mpbird
    cX
    vb
    cA
    vb
    cv
    #
    cC
    cfv
    #
    cixp
    #
    @31
    upixp.1
    vb
    vs
    cA
    @41
    @30
    @40
    @9
    cC
    fveq2
    cbvixpv
    eqtri
    syl6eleqr
    #
    @13
    eqid
    fmptd
    @7
    @18
    va
    cA
    @0
    @1
    @6
    va
    @0
    va
    nfv
    @1
    va
    nfv
    @5
    va
    cA
    nfra1
    nf3an
    @7
    @2
    cA
    wcel
    #
    @18
    @7
    @44
    wa
    #
    vu
    cB
    @2
    @12
    cfv
    #
    cmpt
    vu
    cB
    @35
    cmpt
    @17
    @4
    @45
    vu
    cB
    @46
    @35
    @44
    @46
    @35
    wceq
    @7
    vs
    @2
    @11
    @35
    cA
    @12
    @9
    @2
    wceq
    @8
    @10
    @4
    @9
    @2
    cF
    fveq2
    fveq1d
    @12
    eqid
    @8
    @10
    fvex
    fvmpt3i
    adantl
    mpteq2dv
    @45
    vu
    vx
    cB
    cX
    @12
    @2
    vx
    cv
    #
    cfv
    #
    @46
    @13
    @16
    @7
    @28
    @12
    cX
    wcel
    @44
    @43
    adantlr
    @45
    @13
    eqidd
    @44
    @16
    vx
    cX
    @48
    cmpt
    #
    wceq
    @7
    vw
    @2
    vx
    cX
    vw
    cv
    #
    @47
    cfv
    #
    cmpt
    #
    @49
    cA
    cP
    @50
    @2
    wceq
    vx
    cX
    @51
    @48
    @50
    @2
    @47
    fveq2
    mpteq2dv
    upixp.2
    vx
    cX
    @51
    cX
    @42
    cvv
    upixp.1
    @41
    cvv
    wcel
    #
    vb
    cA
    wral
    @42
    cvv
    wcel
    @53
    vb
    cA
    @40
    cC
    fvex
    rgenw
    vb
    cA
    @41
    cvv
    ixpexg
    ax-mp
    eqeltri
    mptex
    #
    fvmpt3i
    adantl
    @2
    @47
    @12
    fveq1
    fmptco
    @45
    vu
    cB
    @3
    @4
    @7
    @44
    @5
    @6
    @0
    @44
    @5
    wi
    @1
    @5
    va
    cA
    rsp
    3ad2ant3
    imp
    feqmptd
    3eqtr4rd
    ex
    ralrimi
    @7
    @27
    vh
    @7
    @25
    @26
    @7
    @25
    wa
    #
    @20
    vu
    cB
    @8
    @20
    cfv
    #
    cmpt
    @13
    @55
    vu
    cB
    cX
    @20
    @7
    @21
    @24
    simprl
    #
    feqmptd
    @55
    vu
    cB
    @12
    @56
    @55
    @28
    wa
    #
    @12
    vs
    cA
    @9
    @56
    cfv
    #
    cmpt
    #
    @56
    @58
    vs
    cA
    @11
    @59
    @58
    @9
    cA
    wcel
    #
    wa
    #
    @11
    @8
    @9
    cP
    cfv
    #
    @20
    ccom
    #
    cfv
    #
    @56
    @63
    cfv
    #
    @59
    @62
    @8
    @10
    @64
    @58
    @24
    @61
    @10
    @64
    wceq
    #
    @7
    @21
    @24
    @28
    simplrr
    @23
    @67
    va
    @9
    cA
    @38
    @4
    @10
    @22
    @64
    @39
    @38
    @16
    @63
    @20
    @2
    @9
    cP
    fveq2
    coeq1d
    eqeq12d
    rspccva
    sylan
    fveq1d
    @58
    @65
    @66
    wceq
    #
    @61
    @55
    @21
    @28
    @68
    @57
    cB
    cX
    @8
    @63
    @20
    fvco3
    sylan
    adantr
    @62
    @66
    @56
    vx
    cX
    @9
    @47
    cfv
    #
    cmpt
    #
    cfv
    #
    @59
    @62
    @56
    @63
    @70
    @61
    @63
    @70
    wceq
    @58
    vw
    @9
    @52
    @70
    cA
    cP
    @50
    @9
    wceq
    vx
    cX
    @51
    @69
    @50
    @9
    @47
    fveq2
    mpteq2dv
    upixp.2
    @54
    fvmpt3i
    adantl
    fveq1d
    @58
    @71
    @59
    wceq
    #
    @61
    @58
    @56
    cX
    wcel
    #
    @72
    @55
    @21
    @28
    @73
    @57
    cB
    cX
    @8
    @20
    ffvelrn
    sylan
    #
    vx
    @56
    @69
    @59
    cX
    @70
    @9
    @47
    @56
    fveq1
    @70
    eqid
    @9
    @47
    fvex
    fvmpt3i
    syl
    adantr
    eqtrd
    3eqtrd
    mpteq2dva
    @58
    @56
    cA
    wfn
    #
    @56
    @60
    wceq
    @58
    @56
    @42
    wcel
    @75
    @58
    @56
    cX
    @42
    @74
    upixp.1
    syl6eleq
    vb
    cA
    @41
    @56
    ixpfn
    syl
    vs
    cA
    @56
    dffn5
    sylib
    eqtr4d
    mpteq2dva
    eqtr4d
    ex
    alrimiv
    @25
    @15
    @19
    wa
    vh
    @13
    cvv
    @26
    @21
    @15
    @24
    @19
    cB
    cX
    @20
    @13
    feq1
    @26
    @23
    @18
    va
    cA
    @26
    @22
    @17
    @4
    @20
    @13
    @16
    coeq2
    eqeq2d
    ralbidv
    anbi12d
    eqeu
    syl121anc
end
