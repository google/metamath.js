include "cv.mm"
include "com.mm"
include "wcel.mm"
include "cpred.mm"
include "cvv.mm"
include "ciun.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "c0.mm"
include "wceq.mm"
include "csuc.mm"
include "wrex.mm"
include "wo.mm"
include "nn0suc.mm"
include "fr0g.mm"
include "predss.mm"
include "syl6eqss.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "syl5ibr.mm"
include "wa.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrdg.mm"
include "nfres.mm"
include "nffv.mm"
include "nfiun.mm"
include "predeq3.mm"
include "cbviunv.mm"
include "mpteq2i.mm"
include "rdgeq1.mm"
include "reseq1.mm"
include "mp2b.mm"
include "iuneq1.mm"
include "frsucmpt.mm"
include "iunss.mm"
include "a1i.mm"
include "mprgbir.mm"
include "wn.mm"
include "frsucmptn.mm"
include "adantl.mm"
include "0ss.mm"
include "pm2.61dan.mm"
include "adantr.mm"
include "wb.mm"
include "mpbird.mm"
include "rexlimiva.mm"
include "a1d.mm"
include "jaoi.mm"
include "syl.mm"
include "nfvres.mm"
include "pm2.61i.mm"

theorem trpredlem1
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let vi: setvar i
  let cX: class X
  let va: setvar a
  let ve: setvar e
  let vj: setvar j

  disjoint A a
  disjoint A y
  disjoint a y
  disjoint R a
  disjoint R y
  disjoint X a
  disjoint A e
  disjoint A j
  disjoint a e
  disjoint a j
  disjoint e j
  disjoint e y
  disjoint B j
  disjoint i j
  disjoint j y
  disjoint R e
  disjoint R j
  disjoint X e
  disjoint X j
  assert |- ( Pred ( R , A , X ) e. B -> ( ( rec ( ( a e. _V |-> U_ y e. a Pred ( R , A , y ) ) , Pred ( R , A , X ) ) |` _om ) ` i ) C_ A )

  proof
    vi
    cv
    #
    com
    wcel
    #
    cA
    cR
    cX
    cpred
    #
    cB
    wcel
    #
    @0
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
    @2
    crdg
    #
    com
    cres
    #
    cfv
    #
    cA
    wss
    #
    wi
    #
    @1
    @0
    c0
    wceq
    #
    @0
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
    @13
    vj
    @0
    nn0suc
    @14
    @13
    @18
    @3
    @12
    @14
    c0
    @10
    cfv
    #
    cA
    wss
    @3
    @19
    @2
    cA
    @2
    cB
    @8
    fr0g
    cA
    cR
    cX
    predss
    syl6eqss
    @14
    @11
    @19
    cA
    @0
    c0
    @10
    fveq2
    sseq1d
    syl5ibr
    @18
    @12
    @3
    @17
    @12
    vj
    com
    @15
    com
    wcel
    #
    @17
    wa
    @12
    @16
    @10
    cfv
    #
    cA
    wss
    #
    @20
    @22
    @17
    @20
    ve
    @15
    @10
    cfv
    #
    cA
    cR
    ve
    cv
    #
    cpred
    #
    ciun
    #
    cvv
    wcel
    #
    @22
    @20
    @27
    wa
    @21
    @26
    cA
    va
    @2
    @15
    ve
    @4
    @25
    ciun
    #
    @26
    @10
    cvv
    va
    @2
    nfcv
    #
    va
    @15
    nfcv
    #
    ve
    va
    @23
    @25
    va
    @15
    @10
    va
    @9
    com
    va
    @2
    @8
    va
    cvv
    @7
    nfmpt1
    @29
    nfrdg
    va
    com
    nfcv
    nfres
    @30
    nffv
    va
    @25
    nfcv
    nfiun
    #
    @8
    va
    cvv
    @28
    cmpt
    #
    wceq
    @9
    @32
    @2
    crdg
    #
    wceq
    @10
    @33
    com
    cres
    wceq
    va
    cvv
    @7
    @28
    vy
    ve
    @4
    @6
    @25
    cA
    cR
    @5
    @24
    predeq3
    cbviunv
    mpteq2i
    @2
    @8
    @32
    rdgeq1
    @9
    @33
    com
    reseq1
    mp2b
    #
    ve
    @4
    @23
    @25
    iuneq1
    #
    frsucmpt
    @26
    cA
    wss
    @25
    cA
    wss
    #
    ve
    @23
    ve
    @23
    @25
    cA
    iunss
    @36
    @24
    @23
    wcel
    cA
    cR
    @24
    predss
    a1i
    mprgbir
    syl6eqss
    @20
    @27
    wn
    #
    wa
    @21
    c0
    cA
    @37
    @21
    c0
    wceq
    @20
    va
    @2
    @15
    @28
    @26
    @10
    @29
    @30
    @31
    @34
    @35
    frsucmptn
    adantl
    cA
    0ss
    #
    syl6eqss
    pm2.61dan
    adantr
    @17
    @12
    @22
    wb
    @20
    @17
    @11
    @21
    cA
    @0
    @16
    @10
    fveq2
    sseq1d
    adantl
    mpbird
    rexlimiva
    a1d
    jaoi
    syl
    @1
    wn
    #
    @12
    @3
    @39
    @11
    c0
    cA
    @0
    com
    @9
    nfvres
    @38
    syl6eqss
    a1d
    pm2.61i
end
