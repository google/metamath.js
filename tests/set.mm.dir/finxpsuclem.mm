include "com.mm"
include "wcel.mm"
include "c1o.mm"
include "wss.mm"
include "wa.mm"
include "csuc.mm"
include "cfinxp.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cvv.mm"
include "peano2.mm"
include "adantr.mm"
include "wceq.mm"
include "wo.mm"
include "word.mm"
include "wb.mm"
include "1on.mm"
include "onordi.mm"
include "nnord.mm"
include "ordsseleq.mm"
include "sylancr.mm"
include "biimpa.mm"
include "wi.mm"
include "elelsuc.mm"
include "a1i.mm"
include "sucidg.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "mpd.mm"
include "finxpreclem6.mm"
include "syl2anc.mm"
include "sselda.mm"
include "c0.mm"
include "cop.mm"
include "crdg.mm"
include "cuni.mm"
include "c2o.mm"
include "ad2antrr.mm"
include "df-2o.mm"
include "ordsucsssuc.mm"
include "syl5eqss.mm"
include "simpr.mm"
include "finxpreclem4.mm"
include "syl21anc.mm"
include "ordunisuc.mm"
include "syl.mm"
include "opeq1.mm"
include "rdgeq2.mm"
include "fveq12d.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "biantrurd.mm"
include "dffinxpf.mm"
include "abeq2i.mm"
include "syl6rbbr.mm"
include "fvex.mm"
include "opeq2.mm"
include "fveq1d.mm"
include "anbi2d.mm"
include "elab2.mm"
include "baib.mm"
include "3bitr4d.mm"
include "biimpd.mm"
include "impancom.mm"
include "ex.mm"
include "jcad.mm"
include "exbiri.mm"
include "impd.mm"
include "ancomsd.mm"
include "impbid.mm"
include "elxp8.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem finxpsuclem
  let vx: setvar x
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vz: setvar z
  let vy: setvar y
  assume finxpsuclem.1: |- F = ( n e. _om , x e. _V |-> if ( ( n = 1o /\ x e. U ) , (/) , if ( x e. ( _V X. U ) , <. U. n , ( 1st ` x ) >. , <. n , x >. ) ) )

  disjoint N n
  disjoint N x
  disjoint n x
  disjoint U n
  disjoint U x
  disjoint F z
  disjoint N y
  disjoint N z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint U y
  disjoint U z
  assert |- ( ( N e. _om /\ 1o C_ N ) -> ( U ^^ suc N ) = ( ( U ^^ N ) X. U ) )

  proof
    cN
    com
    wcel
    #
    c1o
    cN
    wss
    #
    wa
    #
    vy
    cU
    cN
    csuc
    #
    cfinxp
    #
    cU
    cN
    cfinxp
    #
    cU
    cxp
    #
    @2
    vy
    cv
    #
    @4
    wcel
    #
    @7
    c1st
    cfv
    #
    @5
    wcel
    #
    @7
    cvv
    cU
    cxp
    #
    wcel
    #
    wa
    #
    @7
    @6
    wcel
    @2
    @8
    @13
    @2
    @8
    @10
    @12
    @2
    @8
    @10
    @2
    @8
    wa
    @12
    @10
    @2
    @4
    @11
    @7
    @2
    @3
    com
    wcel
    #
    c1o
    @3
    wcel
    #
    @4
    @11
    wss
    @0
    @14
    @1
    cN
    peano2
    #
    adantr
    @2
    c1o
    cN
    wcel
    #
    c1o
    cN
    wceq
    #
    wo
    #
    @15
    @0
    @1
    @19
    @0
    c1o
    word
    #
    cN
    word
    #
    @1
    @19
    wb
    c1o
    1on
    onordi
    #
    cN
    nnord
    #
    c1o
    cN
    ordsseleq
    sylancr
    biimpa
    @0
    @19
    @15
    wi
    @1
    @0
    @17
    @15
    @18
    @17
    @15
    wi
    @0
    c1o
    cN
    elelsuc
    a1i
    @0
    @15
    @18
    cN
    @3
    wcel
    cN
    com
    sucidg
    c1o
    cN
    @3
    eleq1
    syl5ibrcom
    jaod
    adantr
    mpd
    vx
    cU
    vn
    cF
    @3
    finxpsuclem.1
    finxpreclem6
    syl2anc
    sselda
    #
    @2
    @12
    @8
    @10
    @2
    @12
    wa
    #
    @8
    @10
    @25
    c0
    @3
    cF
    @3
    @7
    cop
    crdg
    cfv
    #
    wceq
    #
    c0
    cN
    cF
    cN
    @9
    cop
    #
    crdg
    #
    cfv
    #
    wceq
    #
    @8
    @10
    @25
    @26
    @30
    c0
    @25
    @26
    @3
    cuni
    #
    cF
    @32
    @9
    cop
    #
    crdg
    #
    cfv
    #
    @30
    @25
    @14
    c2o
    @3
    wss
    #
    @12
    @26
    @35
    wceq
    @0
    @14
    @1
    @12
    @16
    ad2antrr
    @2
    @36
    @12
    @2
    c2o
    c1o
    csuc
    #
    @3
    df-2o
    @0
    @1
    @37
    @3
    wss
    #
    @0
    @20
    @21
    @1
    @38
    wb
    @22
    @23
    c1o
    cN
    ordsucsssuc
    sylancr
    biimpa
    syl5eqss
    adantr
    @2
    @12
    simpr
    vx
    vy
    cU
    vn
    cF
    @3
    finxpsuclem.1
    finxpreclem4
    syl21anc
    @0
    @35
    @30
    wceq
    @1
    @12
    @0
    @32
    cN
    @34
    @29
    @0
    @32
    cN
    wceq
    #
    @34
    @29
    wceq
    #
    @0
    @21
    @39
    @23
    cN
    ordunisuc
    syl
    #
    @39
    @33
    @28
    wceq
    @40
    @32
    cN
    @9
    opeq1
    @33
    @28
    cF
    rdgeq2
    syl
    syl
    @41
    fveq12d
    ad2antrr
    eqtrd
    eqeq2d
    @0
    @8
    @27
    wb
    @1
    @12
    @0
    @27
    @14
    @27
    wa
    #
    @8
    @0
    @14
    @27
    @16
    biantrurd
    @42
    vy
    @4
    vx
    vy
    cU
    vn
    cF
    @3
    finxpsuclem.1
    dffinxpf
    abeq2i
    syl6rbbr
    ad2antrr
    @0
    @10
    @31
    wb
    @1
    @12
    @10
    @0
    @31
    @0
    c0
    cN
    cF
    cN
    vz
    cv
    #
    cop
    #
    crdg
    #
    cfv
    #
    wceq
    #
    wa
    @0
    @31
    wa
    vz
    @9
    @5
    @7
    c1st
    fvex
    @43
    @9
    wceq
    #
    @47
    @31
    @0
    @48
    @46
    @30
    c0
    @48
    cN
    @45
    @29
    @48
    @44
    @28
    wceq
    @45
    @29
    wceq
    @43
    @9
    cN
    opeq2
    @44
    @28
    cF
    rdgeq2
    syl
    fveq1d
    eqeq2d
    anbi2d
    vx
    vz
    cU
    vn
    cF
    cN
    finxpsuclem.1
    dffinxpf
    elab2
    baib
    ad2antrr
    3bitr4d
    #
    biimpd
    impancom
    mpd
    ex
    @2
    @8
    @12
    @24
    ex
    jcad
    @2
    @12
    @10
    @8
    @2
    @12
    @10
    @8
    @2
    @12
    @8
    @10
    @49
    exbiri
    impd
    ancomsd
    impbid
    @7
    @5
    cU
    elxp8
    syl6bbr
    eqrdv
end
