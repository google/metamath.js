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
include "wss.mm"
include "eltrpred.mm"
include "csuc.mm"
include "simplr.mm"
include "peano2.mm"
include "syl.mm"
include "simpr.mm"
include "ssid.mm"
include "wceq.mm"
include "predeq3.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "ssiun.mm"
include "sylancl.mm"
include "wral.mm"
include "fvex.mm"
include "setlikespec.mm"
include "trpredlem1.mm"
include "sseld.mm"
include "wi.mm"
include "expcom.mm"
include "adantl.mm"
include "syld.mm"
include "ralrimiv.mm"
include "ad2antrr.mm"
include "iunexg.mm"
include "sylancr.mm"
include "nfcv.mm"
include "cbviunv.mm"
include "iuneq1.mm"
include "syl5eq.mm"
include "cbvmptv.mm"
include "rdgeq1.mm"
include "reseq1.mm"
include "mp2b.mm"
include "frsucmpt.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"
include "fveq2.mm"
include "dftrpred2.mm"
include "syl6sseqr.mm"
include "ex.mm"
include "rexlimdva.mm"
include "syl5bi.mm"

theorem trpredtr
  let cA: class A
  let cR: class R
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vt: setvar t
  let vy: setvar y


  assert |- ( ( X e. A /\ R Se A ) -> ( Y e. TrPred ( R , A , X ) -> Pred ( R , A , Y ) C_ TrPred ( R , A , X ) ) )

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
    cA
    cR
    cY
    cpred
    #
    @0
    wss
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
    @16
    vi
    com
    @14
    @1
    com
    wcel
    #
    wa
    #
    @11
    @16
    @18
    @11
    wa
    #
    @1
    csuc
    #
    com
    wcel
    #
    @15
    @20
    @9
    cfv
    #
    wss
    #
    @16
    @19
    @17
    @21
    @14
    @17
    @11
    simplr
    #
    @1
    peano2
    syl
    @19
    @15
    vt
    @10
    cA
    cR
    vt
    cv
    #
    cpred
    #
    ciun
    #
    @22
    @19
    @11
    @15
    @15
    wss
    #
    @15
    @27
    wss
    #
    @18
    @11
    simpr
    @15
    ssid
    @11
    @28
    wa
    @15
    @26
    wss
    #
    vt
    @10
    wrex
    @29
    @30
    @28
    vt
    cY
    @10
    @25
    cY
    wceq
    @26
    @15
    @15
    cA
    cR
    @25
    cY
    predeq3
    sseq2d
    rspcev
    vt
    @10
    @26
    @15
    ssiun
    syl
    sylancl
    @19
    @17
    @27
    cvv
    wcel
    #
    @22
    @27
    wceq
    @24
    @19
    @10
    cvv
    wcel
    @26
    cvv
    wcel
    #
    vt
    @10
    wral
    #
    @31
    @1
    @9
    fvex
    @14
    @33
    @17
    @11
    @14
    @32
    vt
    @10
    @14
    @25
    @10
    wcel
    @25
    cA
    wcel
    #
    @32
    @14
    @10
    cA
    @25
    @14
    @7
    cvv
    wcel
    @10
    cA
    wss
    cA
    cR
    cX
    setlikespec
    vy
    cA
    cvv
    cR
    vi
    cX
    va
    trpredlem1
    syl
    sseld
    @13
    @34
    @32
    wi
    @12
    @34
    @13
    @32
    cA
    cR
    @25
    setlikespec
    expcom
    adantl
    syld
    ralrimiv
    ad2antrr
    vt
    @10
    @26
    cvv
    cvv
    iunexg
    sylancr
    vf
    @7
    @1
    vt
    vf
    cv
    #
    @26
    ciun
    #
    @27
    @9
    cvv
    vf
    @7
    nfcv
    vf
    @1
    nfcv
    vf
    @27
    nfcv
    @6
    vf
    cvv
    @36
    cmpt
    #
    wceq
    @8
    @37
    @7
    crdg
    #
    wceq
    @9
    @38
    com
    cres
    wceq
    va
    vf
    cvv
    @5
    @36
    @2
    @35
    wceq
    @5
    vt
    @2
    @26
    ciun
    @36
    vy
    vt
    @2
    @4
    @26
    cA
    cR
    @3
    @25
    predeq3
    cbviunv
    vt
    @2
    @35
    @26
    iuneq1
    syl5eq
    cbvmptv
    @7
    @6
    @37
    rdgeq1
    @8
    @38
    com
    reseq1
    mp2b
    vt
    @35
    @10
    @26
    iuneq1
    frsucmpt
    syl2anc
    sseqtr4d
    @21
    @23
    wa
    #
    @15
    vj
    com
    vj
    cv
    #
    @9
    cfv
    #
    ciun
    #
    @0
    @39
    @15
    @41
    wss
    #
    vj
    com
    wrex
    @15
    @42
    wss
    @43
    @23
    vj
    @20
    com
    @40
    @20
    wceq
    @41
    @22
    @15
    @40
    @20
    @9
    fveq2
    sseq2d
    rspcev
    vj
    com
    @41
    @15
    ssiun
    syl
    vy
    cA
    cR
    vj
    cX
    va
    dftrpred2
    syl6sseqr
    syl2anc
    ex
    rexlimdva
    syl5bi
end
