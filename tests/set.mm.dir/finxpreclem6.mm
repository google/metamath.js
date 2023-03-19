include "com.mm"
include "wcel.mm"
include "c1o.mm"
include "cfinxp.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "wn.mm"
include "anass.mm"
include "c0.mm"
include "cop.mm"
include "crdg.mm"
include "cfv.mm"
include "nfv.mm"
include "cuni.mm"
include "c1st.mm"
include "cif.mm"
include "cmpt2.mm"
include "nfmpt22.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nfrdg.mm"
include "nffv.mm"
include "nfeq2.mm"
include "nfn.mm"
include "nfim.mm"
include "notbid.mm"
include "anbi2d.mm"
include "opeq2.mm"
include "rdgeq2.mm"
include "syl.mm"
include "fveq1d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "vex.mm"
include "csuc.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "opex.mm"
include "rdg0.mm"
include "a1i.mm"
include "con0.mm"
include "nnon.mm"
include "rdgsuc.mm"
include "sylan9eq.mm"
include "finxpreclem5.mm"
include "imp.mm"
include "expl.mm"
include "expcomd.mm"
include "finds2.mm"
include "imbi2d.mm"
include "mpbiri.mm"
include "equcoms.mm"
include "vtocle.mm"
include "syl5bir.mm"
include "anabsi5.mm"
include "wne.mm"
include "opnzi.mm"
include "eqnetrd.mm"
include "necomd.mm"
include "neneqd.mm"
include "chvar.mm"
include "intnand.mm"
include "adantl.mm"
include "wb.mm"
include "cab.mm"
include "abid.mm"
include "opeq1.mm"
include "id.mm"
include "fveq12d.mm"
include "abbidv.mm"
include "dffinxpf.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "syl5rbbr.mm"
include "adantr.mm"
include "mtbird.mm"
include "ex.mm"
include "syl5bi.mm"
include "expdimp.mm"
include "con4d.mm"
include "ssrdv.mm"
include "sylbird.mm"
include "vtocleg.mm"

theorem finxpreclem6
  let vx: setvar x
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vm: setvar m
  let vo: setvar o
  let vy: setvar y
  assume finxpreclem5.1: |- F = ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) , if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) )

  disjoint n x
  disjoint N x
  disjoint N n
  disjoint U n
  disjoint U x
  disjoint F m
  disjoint F o
  disjoint m o
  disjoint N y
  disjoint x y
  disjoint n y
  disjoint U m
  disjoint U o
  disjoint m n
  disjoint m x
  disjoint n o
  disjoint o x
  disjoint U y
  assert |- ( ( N e. _om /\ 1o e. N ) -> ( U ^^ N ) C_ ( _V X. U ) )

  proof
    cN
    com
    wcel
    #
    c1o
    cN
    wcel
    #
    cU
    cN
    cfinxp
    #
    cvv
    cU
    cxp
    #
    wss
    #
    @0
    @1
    wa
    #
    @4
    wi
    vn
    cN
    com
    vn
    cv
    #
    cN
    wceq
    #
    @5
    @6
    com
    wcel
    #
    c1o
    @6
    wcel
    #
    wa
    #
    @4
    @7
    @8
    @0
    @9
    @1
    @6
    cN
    com
    eleq1
    #
    @6
    cN
    c1o
    eleq2
    anbi12d
    @7
    @10
    @4
    @7
    @10
    wa
    #
    vy
    @2
    @3
    @12
    vy
    cv
    #
    @3
    wcel
    #
    @13
    @2
    wcel
    #
    @7
    @10
    @14
    wn
    #
    @15
    wn
    #
    @10
    @16
    wa
    @8
    @9
    @16
    wa
    #
    wa
    #
    @7
    @17
    @8
    @9
    @16
    anass
    @7
    @19
    @17
    @7
    @19
    wa
    @15
    @8
    c0
    @6
    cF
    @6
    @13
    cop
    #
    crdg
    #
    cfv
    #
    wceq
    #
    wa
    #
    @19
    @24
    wn
    @7
    @19
    @23
    @8
    @8
    @9
    vx
    cv
    #
    @3
    wcel
    #
    wn
    #
    wa
    #
    wa
    #
    c0
    @6
    cF
    @6
    @25
    cop
    #
    crdg
    #
    cfv
    #
    wceq
    #
    wn
    #
    wi
    @19
    @23
    wn
    #
    wi
    vx
    vy
    @19
    @35
    vx
    @19
    vx
    nfv
    @23
    vx
    vx
    c0
    @22
    vx
    @6
    @21
    vx
    @20
    cF
    vx
    cF
    vn
    vx
    com
    cvv
    @6
    c1o
    wceq
    @25
    cU
    wcel
    wa
    c0
    @26
    @6
    cuni
    @25
    c1st
    cfv
    cop
    @30
    cif
    cif
    #
    cmpt2
    finxpreclem5.1
    vn
    vx
    com
    cvv
    @36
    nfmpt22
    nfcxfr
    vx
    @20
    nfcv
    nfrdg
    vx
    @6
    nfcv
    nffv
    nfeq2
    nfn
    nfim
    @25
    @13
    wceq
    #
    @29
    @19
    @34
    @35
    @37
    @28
    @18
    @8
    @37
    @27
    @16
    @9
    @37
    @26
    @14
    @25
    @13
    @3
    eleq1
    notbid
    anbi2d
    anbi2d
    @37
    @33
    @23
    @37
    @32
    @22
    c0
    @37
    @6
    @31
    @21
    @37
    @30
    @20
    wceq
    @31
    @21
    wceq
    @25
    @13
    @6
    opeq2
    @30
    @20
    cF
    rdgeq2
    syl
    fveq1d
    eqeq2d
    notbid
    imbi12d
    @29
    c0
    @32
    @29
    @32
    c0
    @29
    @32
    @30
    c0
    @8
    @28
    @32
    @30
    wceq
    #
    @29
    @10
    @27
    wa
    #
    @8
    @38
    @8
    @9
    @27
    anass
    @8
    @39
    @38
    wi
    #
    wi
    #
    vm
    @6
    vn
    vex
    #
    @41
    vn
    vm
    @6
    vm
    cv
    #
    wceq
    #
    @41
    @43
    com
    wcel
    #
    @39
    @43
    @31
    cfv
    #
    @30
    wceq
    #
    wi
    #
    wi
    @47
    c0
    @31
    cfv
    #
    @30
    wceq
    #
    vo
    cv
    #
    @31
    cfv
    #
    @30
    wceq
    #
    @51
    csuc
    #
    @31
    cfv
    #
    @30
    wceq
    #
    @39
    vm
    vo
    @43
    c0
    wceq
    @46
    @49
    @30
    @43
    c0
    @31
    fveq2
    eqeq1d
    @43
    @51
    wceq
    @46
    @52
    @30
    @43
    @51
    @31
    fveq2
    eqeq1d
    @43
    @54
    wceq
    @46
    @55
    @30
    @43
    @54
    @31
    fveq2
    eqeq1d
    @50
    @39
    @30
    cF
    @6
    @25
    opex
    rdg0
    a1i
    @51
    com
    wcel
    #
    @53
    @39
    @56
    @57
    @53
    @39
    @56
    @57
    @53
    wa
    @39
    @55
    @30
    cF
    cfv
    #
    @30
    @57
    @53
    @55
    @52
    cF
    cfv
    #
    @58
    @57
    @51
    con0
    wcel
    @55
    @59
    wceq
    @51
    nnon
    @30
    @51
    cF
    rdgsuc
    syl
    @52
    @30
    cF
    fveq2
    sylan9eq
    @10
    @27
    @58
    @30
    wceq
    vx
    cU
    vn
    cF
    finxpreclem5.1
    finxpreclem5
    imp
    sylan9eq
    expl
    expcomd
    finds2
    @44
    @8
    @45
    @40
    @48
    @6
    @43
    com
    eleq1
    @44
    @38
    @47
    @39
    @44
    @32
    @46
    @30
    @6
    @43
    @31
    fveq2
    eqeq1d
    imbi2d
    imbi12d
    mpbiri
    equcoms
    vtocle
    syl5bir
    anabsi5
    @30
    c0
    wne
    @29
    @6
    @25
    @42
    vx
    vex
    opnzi
    a1i
    eqnetrd
    necomd
    neneqd
    chvar
    intnand
    adantl
    @7
    @15
    @24
    wb
    @19
    @24
    @13
    @24
    vy
    cab
    #
    wcel
    @7
    @15
    @24
    vy
    abid
    @7
    @60
    @2
    @13
    @7
    @60
    @0
    c0
    cN
    cF
    cN
    @13
    cop
    #
    crdg
    #
    cfv
    #
    wceq
    #
    wa
    #
    vy
    cab
    @2
    @7
    @24
    @65
    vy
    @7
    @8
    @0
    @23
    @64
    @11
    @7
    @22
    @63
    c0
    @7
    @6
    cN
    @21
    @62
    @7
    @20
    @61
    wceq
    @21
    @62
    wceq
    @6
    cN
    @13
    opeq1
    @20
    @61
    cF
    rdgeq2
    syl
    @7
    id
    fveq12d
    eqeq2d
    anbi12d
    abbidv
    vx
    vy
    cU
    vn
    cF
    cN
    finxpreclem5.1
    dffinxpf
    syl6eqr
    eleq2d
    syl5rbbr
    adantr
    mtbird
    ex
    syl5bi
    expdimp
    con4d
    ssrdv
    ex
    sylbird
    vtocleg
    anabsi5
end
