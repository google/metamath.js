include "wcel.mm"
include "wse.mm"
include "wa.mm"
include "cv.mm"
include "cpred.mm"
include "wss.mm"
include "wral.mm"
include "ctrpred.mm"
include "com.mm"
include "cvv.mm"
include "ciun.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "cfv.mm"
include "dftrpred2.mm"
include "wi.mm"
include "c0.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "imbi2d.mm"
include "setlikespec.mm"
include "fr0g.mm"
include "syl.mm"
include "adantr.mm"
include "simprr.mm"
include "eqsstrd.mm"
include "fvex.mm"
include "trpredlem1.mm"
include "sseld.mm"
include "expcom.mm"
include "adantl.mm"
include "syld.mm"
include "ralrimiv.mm"
include "ad2antrr.mm"
include "iunexg.mm"
include "sylancr.mm"
include "nfcv.mm"
include "eqid.mm"
include "predeq3.mm"
include "cbviunv.mm"
include "iuneq1.mm"
include "syl5eq.mm"
include "cbvmptv.mm"
include "rdgeq1.mm"
include "reseq1.mm"
include "mp2b.mm"
include "fveq1i.mm"
include "eqeq2i.mm"
include "sylbi.mm"
include "frsucmpt.mm"
include "sylan2.mm"
include "sseq1i.mm"
include "anbi2i.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "ssel.mm"
include "rsp.mm"
include "ad2antrl.mm"
include "sylan9r.mm"
include "ralrimi.mm"
include "sylan2b.mm"
include "iunss.mm"
include "sylibr.mm"
include "exp32.mm"
include "a2d.mm"
include "finds.mm"
include "com12.mm"
include "syl5eqss.mm"

theorem trpredmintr
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cX: class X
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k

  disjoint A y
  disjoint B y
  disjoint R y
  disjoint X y
  disjoint A a
  disjoint A c
  disjoint A d
  disjoint A i
  disjoint A j
  disjoint A k
  disjoint a y
  disjoint c y
  disjoint d y
  disjoint i y
  disjoint j y
  disjoint k y
  disjoint a c
  disjoint a d
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint c d
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint R a
  disjoint R c
  disjoint R d
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint X a
  disjoint X c
  disjoint X i
  disjoint X j
  disjoint X k
  assert |- ( ( ( X e. A /\ R Se A ) /\ ( A. y e. B Pred ( R , A , y ) C_ B /\ Pred ( R , A , X ) C_ B ) ) -> TrPred ( R , A , X ) C_ B )

  proof
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
    vy
    cv
    #
    cpred
    #
    cB
    wss
    #
    vy
    cB
    wral
    #
    cA
    cR
    cX
    cpred
    #
    cB
    wss
    #
    wa
    #
    wa
    #
    cA
    cR
    cX
    ctrpred
    vi
    com
    vi
    cv
    #
    va
    cvv
    vy
    va
    cv
    #
    @4
    ciun
    #
    cmpt
    #
    @7
    crdg
    #
    com
    cres
    #
    cfv
    #
    ciun
    #
    cB
    vy
    cA
    cR
    vi
    cX
    va
    dftrpred2
    @10
    @17
    cB
    wss
    #
    vi
    com
    wral
    @18
    cB
    wss
    @10
    @19
    vi
    com
    @11
    com
    wcel
    @10
    @19
    @10
    vj
    cv
    #
    @16
    cfv
    #
    cB
    wss
    #
    wi
    @10
    c0
    @16
    cfv
    #
    cB
    wss
    #
    wi
    @10
    vk
    cv
    #
    @16
    cfv
    #
    cB
    wss
    #
    wi
    @10
    @25
    csuc
    #
    @16
    cfv
    #
    cB
    wss
    #
    wi
    @10
    @19
    wi
    vj
    vk
    @11
    @20
    c0
    wceq
    #
    @22
    @24
    @10
    @31
    @21
    @23
    cB
    @20
    c0
    @16
    fveq2
    sseq1d
    imbi2d
    @20
    @25
    wceq
    #
    @22
    @27
    @10
    @32
    @21
    @26
    cB
    @20
    @25
    @16
    fveq2
    sseq1d
    imbi2d
    @20
    @28
    wceq
    #
    @22
    @30
    @10
    @33
    @21
    @29
    cB
    @20
    @28
    @16
    fveq2
    sseq1d
    imbi2d
    @20
    @11
    wceq
    #
    @22
    @19
    @10
    @34
    @21
    @17
    cB
    @20
    @11
    @16
    fveq2
    sseq1d
    imbi2d
    @10
    @23
    @7
    cB
    @2
    @23
    @7
    wceq
    #
    @9
    @2
    @7
    cvv
    wcel
    #
    @35
    cA
    cR
    cX
    setlikespec
    #
    @7
    cvv
    @14
    fr0g
    syl
    adantr
    @2
    @6
    @8
    simprr
    eqsstrd
    @25
    com
    wcel
    #
    @10
    @27
    @30
    @38
    @10
    @27
    @30
    @38
    @10
    @27
    wa
    #
    wa
    #
    @29
    vy
    @25
    vc
    cvv
    vd
    vc
    cv
    #
    cA
    cR
    vd
    cv
    #
    cpred
    #
    ciun
    #
    cmpt
    #
    @7
    crdg
    #
    com
    cres
    #
    cfv
    #
    @4
    ciun
    #
    cB
    @39
    @38
    @49
    cvv
    wcel
    #
    @29
    @49
    wceq
    @39
    @48
    cvv
    wcel
    @4
    cvv
    wcel
    #
    vy
    @48
    wral
    #
    @50
    @25
    @47
    fvex
    @2
    @52
    @9
    @27
    @2
    @51
    vy
    @48
    @2
    @3
    @48
    wcel
    #
    @3
    cA
    wcel
    #
    @51
    @2
    @48
    cA
    @3
    @2
    @36
    @48
    cA
    wss
    @37
    vd
    cA
    cvv
    cR
    vk
    cX
    vc
    trpredlem1
    syl
    sseld
    @1
    @54
    @51
    wi
    @0
    @54
    @1
    @51
    cA
    cR
    @3
    setlikespec
    expcom
    adantl
    syld
    ralrimiv
    ad2antrr
    vy
    @48
    @4
    cvv
    cvv
    iunexg
    sylancr
    va
    @7
    @25
    @13
    @49
    @16
    cvv
    va
    @7
    nfcv
    va
    @25
    nfcv
    va
    @49
    nfcv
    @16
    eqid
    @12
    @26
    wceq
    @12
    @48
    wceq
    @13
    @49
    wceq
    @26
    @48
    @12
    @25
    @16
    @47
    @14
    @45
    wceq
    @15
    @46
    wceq
    @16
    @47
    wceq
    va
    vc
    cvv
    @13
    @44
    @12
    @41
    wceq
    @13
    vd
    @12
    @43
    ciun
    @44
    vy
    vd
    @12
    @4
    @43
    cA
    cR
    @3
    @42
    predeq3
    cbviunv
    vd
    @12
    @41
    @43
    iuneq1
    syl5eq
    cbvmptv
    @7
    @14
    @45
    rdgeq1
    @15
    @46
    com
    reseq1
    mp2b
    fveq1i
    #
    eqeq2i
    vy
    @12
    @48
    @4
    iuneq1
    sylbi
    frsucmpt
    sylan2
    @40
    @5
    vy
    @48
    wral
    #
    @49
    cB
    wss
    @39
    @38
    @10
    @48
    cB
    wss
    #
    wa
    #
    @56
    @27
    @57
    @10
    @26
    @48
    cB
    @55
    sseq1i
    anbi2i
    @58
    @56
    @38
    @58
    @5
    vy
    @48
    @10
    @57
    vy
    @2
    @9
    vy
    @2
    vy
    nfv
    @6
    @8
    vy
    @5
    vy
    cB
    nfra1
    @8
    vy
    nfv
    nfan
    nfan
    @57
    vy
    nfv
    nfan
    @57
    @53
    @3
    cB
    wcel
    #
    @10
    @5
    @48
    cB
    @3
    ssel
    @6
    @59
    @5
    wi
    @2
    @8
    @5
    vy
    cB
    rsp
    ad2antrl
    sylan9r
    ralrimi
    adantl
    sylan2b
    vy
    @48
    @4
    cB
    iunss
    sylibr
    eqsstrd
    exp32
    a2d
    finds
    com12
    ralrimiv
    vi
    com
    @17
    cB
    iunss
    sylibr
    syl5eqss
end
