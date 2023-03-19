include "ctrpred.mm"
include "wcel.mm"
include "cv.mm"
include "cvv.mm"
include "cpred.mm"
include "ciun.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "cfv.mm"
include "wrex.mm"
include "wse.mm"
include "wa.mm"
include "wbr.mm"
include "wo.mm"
include "eltrpred.mm"
include "c0.mm"
include "wceq.mm"
include "csuc.mm"
include "wi.mm"
include "nn0suc.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "anbi2d.mm"
include "biimpd.mm"
include "setlikespec.mm"
include "fr0g.mm"
include "syl.mm"
include "biimpa.mm"
include "syl6com.mm"
include "wral.mm"
include "fvex.mm"
include "wss.mm"
include "trpredlem1.mm"
include "sseld.mm"
include "expcom.mm"
include "adantl.mm"
include "syld.mm"
include "ralrimiv.mm"
include "iunexg.mm"
include "sylancr.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrdg.mm"
include "nfres.mm"
include "nffv.mm"
include "nfiun.mm"
include "eqid.mm"
include "predeq3.mm"
include "cbviunv.mm"
include "iuneq1.mm"
include "syl5eq.mm"
include "frsucmpt.mm"
include "sylan2.mm"
include "expimpd.mm"
include "eliun.mm"
include "ssiun2.mm"
include "dftrpred2.mm"
include "syl6sseqr.mm"
include "vex.mm"
include "elpredim.mm"
include "a1i.mm"
include "anim12d.mm"
include "reximdv2.mm"
include "com12.mm"
include "sylbi.mm"
include "pm2.43d.mm"
include "com23.mm"
include "rexlimdv.mm"
include "orim12d.mm"
include "ex.mm"
include "syl5.mm"
include "syl5bi.mm"

theorem trpredrec
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vi: setvar i
  let vj: setvar j
  let vy: setvar y

  disjoint A z
  disjoint R z
  disjoint X z
  disjoint Y z
  disjoint A a
  disjoint A i
  disjoint A j
  disjoint A y
  disjoint a i
  disjoint a j
  disjoint a y
  disjoint a z
  disjoint i j
  disjoint i y
  disjoint i z
  disjoint j y
  disjoint j z
  disjoint y z
  disjoint R a
  disjoint R i
  disjoint R j
  disjoint R y
  disjoint X a
  disjoint X i
  disjoint X j
  disjoint X y
  disjoint Y a
  disjoint Y i
  disjoint Y j
  disjoint Y y
  assert |- ( ( X e. A /\ R Se A ) -> ( Y e. TrPred ( R , A , X ) -> ( Y e. Pred ( R , A , X ) \/ E. z e. TrPred ( R , A , X ) Y R z ) ) )

  proof
    cY
    cA
    cR
    cX
    ctrpred
    #
    wcel
    cY
    vi
    cv
    #
    va
    cvv
    vy
    va
    cv
    #
    cA
    cR
    vy
    cv
    #
    cpred
    #
    ciun
    #
    cmpt
    #
    cA
    cR
    cX
    cpred
    #
    crdg
    #
    com
    cres
    #
    cfv
    #
    wcel
    #
    vi
    com
    wrex
    cX
    cA
    wcel
    #
    cA
    cR
    wse
    #
    wa
    #
    cY
    @7
    wcel
    #
    cY
    vz
    cv
    #
    cR
    wbr
    #
    vz
    @0
    wrex
    #
    wo
    #
    vy
    cA
    cR
    vi
    cX
    cY
    va
    eltrpred
    @14
    @11
    @19
    vi
    com
    @1
    com
    wcel
    @1
    c0
    wceq
    #
    @1
    vj
    cv
    #
    csuc
    #
    wceq
    #
    vj
    com
    wrex
    #
    wo
    #
    @14
    @11
    @19
    wi
    vj
    @1
    nn0suc
    @14
    @11
    @25
    @19
    @14
    @11
    @25
    @19
    wi
    @14
    @11
    wa
    #
    @20
    @15
    @24
    @18
    @20
    @26
    @14
    cY
    c0
    @9
    cfv
    #
    wcel
    #
    wa
    #
    @15
    @20
    @26
    @29
    @20
    @11
    @28
    @14
    @20
    @10
    @27
    cY
    @1
    c0
    @9
    fveq2
    eleq2d
    anbi2d
    biimpd
    @14
    @28
    @15
    @14
    @27
    @7
    cY
    @14
    @7
    cvv
    wcel
    #
    @27
    @7
    wceq
    cA
    cR
    cX
    setlikespec
    #
    @7
    cvv
    @6
    fr0g
    syl
    eleq2d
    biimpa
    syl6com
    @26
    @23
    @18
    vj
    com
    @26
    @23
    @21
    com
    wcel
    #
    @18
    @23
    @26
    @14
    cY
    @22
    @9
    cfv
    #
    wcel
    #
    wa
    #
    @32
    @18
    wi
    #
    @23
    @26
    @35
    @23
    @11
    @34
    @14
    @23
    @10
    @33
    cY
    @1
    @22
    @9
    fveq2
    eleq2d
    anbi2d
    biimpd
    @35
    @32
    @18
    @32
    @35
    cY
    vz
    @21
    @9
    cfv
    #
    cA
    cR
    @16
    cpred
    #
    ciun
    #
    wcel
    #
    @36
    @32
    @14
    @34
    @40
    @32
    @14
    wa
    #
    @34
    @40
    @41
    @33
    @39
    cY
    @14
    @32
    @39
    cvv
    wcel
    #
    @33
    @39
    wceq
    @14
    @37
    cvv
    wcel
    @38
    cvv
    wcel
    #
    vz
    @37
    wral
    @42
    @21
    @9
    fvex
    @14
    @43
    vz
    @37
    @14
    @16
    @37
    wcel
    #
    @16
    cA
    wcel
    #
    @43
    @14
    @37
    cA
    @16
    @14
    @30
    @37
    cA
    wss
    @31
    vy
    cA
    cvv
    cR
    vj
    cX
    va
    trpredlem1
    syl
    sseld
    @13
    @45
    @43
    wi
    @12
    @45
    @13
    @43
    cA
    cR
    @16
    setlikespec
    expcom
    adantl
    syld
    ralrimiv
    vz
    @37
    @38
    cvv
    cvv
    iunexg
    sylancr
    va
    @7
    @21
    @5
    @39
    @9
    cvv
    va
    @7
    nfcv
    #
    va
    @21
    nfcv
    #
    vz
    va
    @37
    @38
    va
    @21
    @9
    va
    @8
    com
    va
    @7
    @6
    va
    cvv
    @5
    nfmpt1
    @46
    nfrdg
    va
    com
    nfcv
    nfres
    @47
    nffv
    va
    @38
    nfcv
    nfiun
    @9
    eqid
    @2
    @37
    wceq
    @5
    vz
    @2
    @38
    ciun
    @39
    vy
    vz
    @2
    @4
    @38
    cA
    cR
    @3
    @16
    predeq3
    cbviunv
    vz
    @2
    @37
    @38
    iuneq1
    syl5eq
    frsucmpt
    sylan2
    eleq2d
    biimpd
    expimpd
    @40
    cY
    @38
    wcel
    #
    vz
    @37
    wrex
    #
    @36
    vz
    cY
    @37
    @38
    eliun
    @32
    @49
    @18
    @32
    @48
    @17
    vz
    @37
    @0
    @32
    @44
    @16
    @0
    wcel
    @48
    @17
    @32
    @37
    @0
    @16
    @32
    @37
    vj
    com
    @37
    ciun
    @0
    vj
    com
    @37
    ssiun2
    vy
    cA
    cR
    vj
    cX
    va
    dftrpred2
    syl6sseqr
    sseld
    @48
    @17
    wi
    @32
    cA
    cR
    @16
    cY
    vz
    vex
    elpredim
    a1i
    anim12d
    reximdv2
    com12
    sylbi
    syl6com
    pm2.43d
    syl6com
    com23
    rexlimdv
    orim12d
    ex
    com23
    syl5
    rexlimdv
    syl5bi
end
