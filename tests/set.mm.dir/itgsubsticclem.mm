include "cdit.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cv.mm"
include "fveq2.mm"
include "nfcv.mm"
include "cr.mm"
include "cicc.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "cbvditg.mm"
include "cioo.mm"
include "wa.mm"
include "cc.mm"
include "wceq.mm"
include "wss.mm"
include "iccssred.mm"
include "adantr.mm"
include "ioossicc.mm"
include "sseli.mm"
include "adantl.mm"
include "sseldd.mm"
include "iftrued.mm"
include "a1i.mm"
include "ccncf.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "feq1dd.mm"
include "mptex2.mm"
include "syldan.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "3eqtrd.mm"
include "ditgeq3d.mm"
include "cpnf.mm"
include "cmnf.mm"
include "cxr.mm"
include "mnfxr.mm"
include "pnfxr.mm"
include "ioomax.mm"
include "eqcomi.mm"
include "sseqtrd.mm"
include "ax-resscn.mm"
include "syl6eqssr.mm"
include "cncfss.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crn.mm"
include "crest.mm"
include "cuni.mm"
include "ctg.mm"
include "ccn.mm"
include "cres.mm"
include "eqid.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "syl6ss.mm"
include "ssid.mm"
include "unicntop.mm"
include "restid.mm"
include "ax-mp.mm"
include "cncfcn.mm"
include "sylancl.mm"
include "cvv.mm"
include "reex.mm"
include "restabs.mm"
include "syl3anc.mm"
include "tgioo2.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "icccncfext.mm"
include "simpld.mm"
include "uniretop.mm"
include "cnf.mm"
include "feq2d.mm"
include "mpbid.mm"
include "feqmptd.mm"
include "frn.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "eqcomd.mm"
include "eqeltrrd.mm"
include "itgsubst.mm"
include "3eqtr3a.mm"
include "simpr.mm"
include "wral.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "resttopon.mm"
include "sylancr.mm"
include "cnf2.mm"
include "fmpt.mm"
include "sylibr.mm"
include "rsp.mm"
include "sylc.mm"
include "simpll.mm"
include "wex.mm"
include "elex.mm"
include "isset.mm"
include "sylib.mm"
include "exlimddv.mm"
include "fvmptd.mm"

theorem itgsubsticclem
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vk: setvar k
  assume itgsubsticclem.1: |- F = ( u e. ( K [,] L ) |-> C )
  assume itgsubsticclem.2: |- G = ( u e. RR |-> if ( u e. ( K [,] L ) , ( F ` u ) , if ( u < K , ( F ` K ) , ( F ` L ) ) ) )
  assume itgsubsticclem.3: |- ( ph -> X e. RR )
  assume itgsubsticclem.4: |- ( ph -> Y e. RR )
  assume itgsubsticclem.5: |- ( ph -> X <_ Y )
  assume itgsubsticclem.6: |- ( ph -> ( x e. ( X [,] Y ) |-> A ) e. ( ( X [,] Y ) -cn-> ( K [,] L ) ) )
  assume itgsubsticclem.7: |- ( ph -> ( x e. ( X (,) Y ) |-> B ) e. ( ( ( X (,) Y ) -cn-> CC ) i^i L^1 ) )
  assume itgsubsticclem.8: |- ( ph -> F e. ( ( K [,] L ) -cn-> CC ) )
  assume itgsubsticclem.9: |- ( ph -> K e. RR )
  assume itgsubsticclem.10: |- ( ph -> L e. RR )
  assume itgsubsticclem.11: |- ( ph -> K <_ L )
  assume itgsubsticclem.12: |- ( ph -> ( RR _D ( x e. ( X [,] Y ) |-> A ) ) = ( x e. ( X (,) Y ) |-> B ) )
  assume itgsubsticclem.13: |- ( u = A -> C = E )
  assume itgsubsticclem.14: |- ( x = X -> A = K )
  assume itgsubsticclem.15: |- ( x = Y -> A = L )

  disjoint A u
  disjoint E u
  disjoint G x
  disjoint K u
  disjoint K x
  disjoint u x
  disjoint L u
  disjoint L x
  disjoint X u
  disjoint X x
  disjoint Y u
  disjoint Y x
  disjoint ph u
  disjoint ph x
  disjoint A w
  disjoint u w
  disjoint G w
  disjoint w x
  disjoint K w
  disjoint L w
  disjoint X w
  disjoint Y w
  disjoint ph w
  disjoint k x
  assert |- ( ph -> S_ [ K -> L ] C _d u = S_ [ X -> Y ] ( E x. B ) _d x )

  proof
    wph
    vu
    cK
    cL
    cC
    cdit
    #
    vx
    cX
    cY
    cA
    cG
    cfv
    #
    cB
    cmul
    co
    #
    cdit
    #
    vx
    cX
    cY
    cE
    cB
    cmul
    co
    #
    cdit
    wph
    vu
    cK
    cL
    vu
    cv
    #
    cG
    cfv
    #
    cdit
    vw
    cK
    cL
    vw
    cv
    #
    cG
    cfv
    #
    cdit
    @0
    @3
    vu
    vw
    cK
    cL
    @6
    @8
    @5
    @7
    cG
    fveq2
    vw
    @6
    nfcv
    vu
    @7
    cG
    vu
    cG
    vu
    cr
    @5
    cK
    cL
    cicc
    co
    #
    wcel
    #
    @5
    cF
    cfv
    #
    @5
    cK
    clt
    wbr
    cK
    cF
    cfv
    cL
    cF
    cfv
    cif
    #
    cif
    #
    cmpt
    #
    itgsubsticclem.2
    vu
    cr
    @13
    nfmpt1
    nfcxfr
    vu
    @7
    nfcv
    nffv
    cbvditg
    wph
    vu
    cK
    cL
    @6
    cC
    itgsubsticclem.11
    wph
    @5
    cK
    cL
    cioo
    co
    #
    wcel
    #
    wa
    #
    @6
    @13
    @11
    cC
    @17
    @5
    cr
    wcel
    @13
    cc
    wcel
    @6
    @13
    wceq
    @17
    @9
    cr
    @5
    wph
    @9
    cr
    wss
    #
    @16
    wph
    cK
    cL
    itgsubsticclem.9
    itgsubsticclem.10
    iccssred
    #
    adantr
    @16
    @10
    wph
    @15
    @9
    @5
    cK
    cL
    ioossicc
    sseli
    adantl
    #
    sseldd
    @17
    @13
    @11
    cc
    @17
    @10
    @11
    @12
    @20
    iftrued
    #
    @17
    @11
    cC
    cc
    @17
    @10
    cC
    cc
    wcel
    #
    @11
    cC
    wceq
    #
    @20
    wph
    @16
    @10
    @22
    @20
    wph
    vu
    @9
    cC
    cc
    wph
    @9
    cc
    cF
    vu
    @9
    cC
    cmpt
    #
    cF
    @24
    wceq
    wph
    itgsubsticclem.1
    a1i
    wph
    cF
    @9
    cc
    ccncf
    co
    #
    wcel
    @9
    cc
    cF
    wf
    #
    itgsubsticclem.8
    @9
    cc
    cF
    cncff
    syl
    #
    feq1dd
    mptex2
    #
    syldan
    #
    vu
    @9
    cC
    cc
    cF
    itgsubsticclem.1
    fvmpt2
    #
    syl2anc
    #
    @29
    eqeltrd
    eqeltrd
    vu
    cr
    @13
    cc
    cG
    itgsubsticclem.2
    fvmpt2
    syl2anc
    @21
    @31
    3eqtrd
    ditgeq3d
    wph
    vx
    vw
    cA
    cB
    @8
    @1
    cK
    cL
    cpnf
    cX
    cY
    cmnf
    itgsubsticclem.3
    itgsubsticclem.4
    itgsubsticclem.5
    cmnf
    cxr
    wcel
    wph
    mnfxr
    a1i
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    wph
    cX
    cY
    cicc
    co
    #
    @9
    ccncf
    co
    #
    @32
    cmnf
    cpnf
    cioo
    co
    #
    ccncf
    co
    #
    vx
    @32
    cA
    cmpt
    #
    wph
    @9
    @34
    wss
    @34
    cc
    wss
    #
    @33
    @35
    wss
    wph
    @9
    cr
    @34
    @19
    cr
    @34
    wceq
    wph
    @34
    cr
    ioomax
    eqcomi
    #
    a1i
    #
    sseqtrd
    wph
    @34
    cr
    cc
    @39
    ax-resscn
    syl6eqssr
    #
    @32
    @9
    @34
    cncfss
    syl2anc
    itgsubsticclem.6
    sseldd
    itgsubsticclem.7
    wph
    cG
    vw
    @34
    @8
    cmpt
    @34
    cc
    ccncf
    co
    #
    wph
    vw
    @34
    ccnfld
    ctopn
    cfv
    #
    cF
    crn
    #
    crest
    co
    #
    cuni
    #
    cG
    wph
    cr
    @45
    cG
    wf
    #
    @34
    @45
    cG
    wf
    wph
    cG
    cioo
    crn
    ctg
    cfv
    #
    @44
    ccn
    co
    #
    wcel
    #
    @46
    wph
    @49
    cG
    @9
    cres
    cF
    wceq
    wph
    vu
    cK
    cL
    cF
    cG
    @47
    @42
    @42
    cuni
    #
    vu
    cF
    @24
    itgsubsticclem.1
    vu
    @9
    cC
    nfmpt1
    nfcxfr
    @47
    eqid
    @50
    eqid
    itgsubsticclem.2
    itgsubsticclem.9
    itgsubsticclem.10
    itgsubsticclem.11
    @42
    ctop
    wcel
    #
    wph
    @42
    @42
    eqid
    #
    cnfldtop
    #
    a1i
    #
    wph
    cF
    @25
    @47
    @9
    crest
    co
    #
    @42
    ccn
    co
    #
    itgsubsticclem.8
    wph
    @25
    @42
    @9
    crest
    co
    #
    @42
    ccn
    co
    #
    @56
    wph
    @9
    cc
    wss
    #
    cc
    cc
    wss
    #
    @25
    @58
    wceq
    wph
    @9
    cr
    cc
    @19
    ax-resscn
    syl6ss
    #
    cc
    ssid
    #
    @9
    cc
    @42
    @57
    @42
    @52
    @57
    eqid
    #
    @42
    cc
    crest
    co
    #
    @42
    @51
    @64
    @42
    wceq
    @53
    @42
    ctop
    cc
    unicntop
    restid
    ax-mp
    eqcomi
    cncfcn
    sylancl
    wph
    @57
    @55
    @42
    ccn
    wph
    @42
    cr
    crest
    co
    #
    @9
    crest
    co
    #
    @57
    @55
    wph
    @51
    @18
    cr
    cvv
    wcel
    #
    @66
    @57
    wceq
    @54
    @19
    @67
    wph
    reex
    a1i
    @9
    cr
    @42
    ctop
    cvv
    restabs
    syl3anc
    wph
    @65
    @47
    @9
    crest
    @65
    @47
    wceq
    wph
    @47
    @65
    @42
    @52
    tgioo2
    #
    eqcomi
    a1i
    oveq1d
    eqtr3d
    oveq1d
    eqtrd
    eleqtrd
    icccncfext
    simpld
    #
    cG
    @47
    @44
    cr
    @45
    uniretop
    @45
    eqid
    cnf
    syl
    wph
    cr
    @34
    @45
    cG
    @39
    feq2d
    mpbid
    feqmptd
    wph
    @34
    @43
    ccncf
    co
    #
    @41
    cG
    wph
    @43
    cc
    wss
    #
    @60
    @70
    @41
    wss
    wph
    @26
    @71
    @27
    @9
    cc
    cF
    frn
    syl
    #
    @62
    @34
    @43
    cc
    cncfss
    sylancl
    wph
    cG
    @48
    @70
    @69
    wph
    @70
    @48
    wph
    @37
    @71
    @70
    @48
    wceq
    @40
    @72
    @34
    @43
    @42
    @47
    @44
    @52
    @47
    @65
    @42
    @34
    crest
    co
    @68
    cr
    @34
    @42
    crest
    @38
    oveq2i
    eqtri
    @44
    eqid
    cncfcn
    syl2anc
    eqcomd
    eleqtrd
    sseldd
    eqeltrrd
    itgsubsticclem.12
    @7
    cA
    cG
    fveq2
    itgsubsticclem.14
    itgsubsticclem.15
    itgsubst
    3eqtr3a
    wph
    vx
    cX
    cY
    @2
    @4
    itgsubsticclem.5
    wph
    vx
    cv
    #
    cX
    cY
    cioo
    co
    #
    wcel
    #
    wa
    #
    @1
    cE
    cB
    cmul
    @76
    vu
    cA
    @13
    cE
    cr
    cG
    cc
    cG
    @14
    wceq
    @76
    itgsubsticclem.2
    a1i
    @76
    @5
    cA
    wceq
    #
    wa
    #
    @13
    @11
    cC
    cE
    @78
    @10
    @11
    @12
    @78
    @5
    cA
    @9
    @76
    @77
    simpr
    @76
    cA
    @9
    wcel
    #
    @77
    @76
    @79
    vx
    @32
    wral
    #
    @73
    @32
    wcel
    #
    @79
    @76
    @32
    @9
    @36
    wf
    #
    @80
    wph
    @82
    @75
    wph
    @42
    @32
    crest
    co
    #
    @32
    ctopon
    cfv
    wcel
    #
    @57
    @9
    ctopon
    cfv
    wcel
    #
    @36
    @83
    @57
    ccn
    co
    #
    wcel
    @82
    wph
    @42
    cc
    ctopon
    cfv
    wcel
    #
    @32
    cc
    wss
    #
    @84
    @42
    @52
    cnfldtopon
    #
    wph
    @32
    cr
    cc
    wph
    cX
    cY
    itgsubsticclem.3
    itgsubsticclem.4
    iccssred
    ax-resscn
    syl6ss
    #
    @32
    @42
    cc
    resttopon
    sylancr
    wph
    @87
    @59
    @85
    @89
    @61
    @9
    @42
    cc
    resttopon
    sylancr
    wph
    @36
    @33
    @86
    itgsubsticclem.6
    wph
    @88
    @59
    @33
    @86
    wceq
    @90
    @61
    @32
    @9
    @42
    @83
    @57
    @52
    @83
    eqid
    @63
    cncfcn
    syl2anc
    eleqtrd
    @36
    @83
    @57
    @32
    @9
    cnf2
    syl3anc
    adantr
    vx
    @32
    @9
    cA
    @36
    @36
    eqid
    fmpt
    sylibr
    @75
    @81
    wph
    @74
    @32
    @73
    cX
    cY
    ioossicc
    sseli
    adantl
    @79
    vx
    @32
    rsp
    sylc
    #
    adantr
    eqeltrd
    #
    iftrued
    @78
    @10
    @22
    @23
    @92
    @78
    wph
    @10
    @22
    wph
    @75
    @77
    simpll
    @92
    @28
    syl2anc
    #
    @30
    syl2anc
    @77
    cC
    cE
    wceq
    @76
    itgsubsticclem.13
    adantl
    #
    3eqtrd
    @76
    @9
    cr
    cA
    wph
    @18
    @75
    @19
    adantr
    @91
    sseldd
    @76
    @77
    cE
    cc
    wcel
    vu
    @76
    cA
    cvv
    wcel
    #
    @77
    vu
    wex
    @76
    @79
    @95
    @91
    cA
    @9
    elex
    syl
    vu
    cA
    isset
    sylib
    @78
    cC
    cE
    cc
    @94
    @93
    eqeltrrd
    exlimddv
    fvmptd
    oveq1d
    ditgeq3d
    eqtrd
end
