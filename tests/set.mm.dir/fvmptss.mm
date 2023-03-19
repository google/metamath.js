include "wss.mm"
include "wral.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "dmmptss.mm"
include "sseli.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "imbi2d.mm"
include "nfcv.mm"
include "nfra1.mm"
include "cmpt.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfss.mm"
include "nfim.mm"
include "wa.mm"
include "cvv.mm"
include "dmmpt.mm"
include "rabeq2i.mm"
include "fvmpt2.mm"
include "eqimss.mm"
include "syl.mm"
include "sylbi.mm"
include "wn.mm"
include "c0.mm"
include "ndmfv.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"
include "rsp.mm"
include "impcom.mm"
include "syl5ss.mm"
include "ex.mm"
include "vtoclgaf.mm"
include "vtoclga.mm"
include "sylan2.mm"
include "adantl.mm"
include "pm2.61dan.mm"

theorem fvmptss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vy: setvar y
  assume mptrcl.1: |- F = ( x e. A |-> B )

  disjoint A x
  disjoint C x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint D y
  disjoint F y
  disjoint C y
  assert |- ( A. x e. A B C_ C -> ( F ` D ) C_ C )

  proof
    cB
    cC
    wss
    #
    vx
    cA
    wral
    #
    cD
    cF
    cdm
    #
    wcel
    #
    cD
    cF
    cfv
    #
    cC
    wss
    #
    @3
    @1
    cD
    cA
    wcel
    #
    @5
    @2
    cA
    cD
    vx
    cA
    cB
    cF
    mptrcl.1
    dmmptss
    sseli
    @6
    @1
    @5
    @1
    vy
    cv
    #
    cF
    cfv
    #
    cC
    wss
    #
    wi
    #
    @1
    @5
    wi
    vy
    cD
    cA
    @7
    cD
    wceq
    #
    @9
    @5
    @1
    @11
    @8
    @4
    cC
    @7
    cD
    cF
    fveq2
    sseq1d
    imbi2d
    @1
    vx
    cv
    #
    cF
    cfv
    #
    cC
    wss
    #
    wi
    @10
    vx
    @7
    cA
    vx
    @7
    nfcv
    #
    @1
    @9
    vx
    @0
    vx
    cA
    nfra1
    vx
    @8
    cC
    vx
    @7
    cF
    vx
    cF
    vx
    cA
    cB
    cmpt
    mptrcl.1
    vx
    cA
    cB
    nfmpt1
    nfcxfr
    @15
    nffv
    vx
    cC
    nfcv
    nfss
    nfim
    @12
    @7
    wceq
    #
    @14
    @9
    @1
    @16
    @13
    @8
    cC
    @12
    @7
    cF
    fveq2
    sseq1d
    imbi2d
    @12
    cA
    wcel
    #
    @1
    @14
    @17
    @1
    wa
    @13
    cB
    cC
    @12
    @2
    wcel
    #
    @13
    cB
    wss
    #
    @18
    @17
    cB
    cvv
    wcel
    #
    wa
    #
    @19
    @20
    vx
    @2
    cA
    vx
    cA
    cB
    cF
    mptrcl.1
    dmmpt
    rabeq2i
    @21
    @13
    cB
    wceq
    @19
    vx
    cA
    cB
    cvv
    cF
    mptrcl.1
    fvmpt2
    @13
    cB
    eqimss
    syl
    sylbi
    @18
    wn
    @13
    c0
    cB
    @12
    cF
    ndmfv
    cB
    0ss
    syl6eqss
    pm2.61i
    @1
    @17
    @0
    @0
    vx
    cA
    rsp
    impcom
    syl5ss
    ex
    vtoclgaf
    vtoclga
    impcom
    sylan2
    @1
    @3
    wn
    #
    wa
    @4
    c0
    cC
    @22
    @4
    c0
    wceq
    @1
    cD
    cF
    ndmfv
    adantl
    cC
    0ss
    syl6eqss
    pm2.61dan
end
