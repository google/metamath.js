include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cdm.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "dmmptss.mm"
include "sseli.mm"
include "cid.mm"
include "cmpt.mm"
include "eqid.mm"
include "fvmptex.mm"
include "fvex.mm"
include "nfcv.mm"
include "nffv.mm"
include "cv.mm"
include "fveq2d.mm"
include "fvmptf.mm"
include "mpan2.mm"
include "syl5eq.mm"
include "fvprc.mm"
include "sylan9eq.mm"
include "expcom.mm"
include "syl5.mm"
include "ndmfv.mm"
include "pm2.61d1.mm"

theorem fvmptnf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume fvmptf.1: |- F/_ x A
  assume fvmptf.2: |- F/_ x C
  assume fvmptf.3: |- ( x = A -> B = C )
  assume fvmptf.4: |- F = ( x e. D |-> B )

  disjoint D x
  assert |- ( -. C e. _V -> ( F ` A ) = (/) )

  proof
    cC
    cvv
    wcel
    wn
    #
    cA
    cF
    cdm
    #
    wcel
    #
    cA
    cF
    cfv
    #
    c0
    wceq
    #
    @2
    cA
    cD
    wcel
    #
    @0
    @4
    @1
    cD
    cA
    vx
    cD
    cB
    cF
    fvmptf.4
    dmmptss
    sseli
    @5
    @0
    @4
    @5
    @0
    @3
    cC
    cid
    cfv
    #
    c0
    @5
    @3
    cA
    vx
    cD
    cB
    cid
    cfv
    #
    cmpt
    #
    cfv
    #
    @6
    vx
    cD
    cB
    cA
    cF
    @8
    fvmptf.4
    @8
    eqid
    #
    fvmptex
    @5
    @6
    cvv
    wcel
    @9
    @6
    wceq
    cC
    cid
    fvex
    vx
    cA
    @7
    @6
    cD
    @8
    cvv
    fvmptf.1
    vx
    cC
    cid
    vx
    cid
    nfcv
    fvmptf.2
    nffv
    vx
    cv
    cA
    wceq
    cB
    cC
    cid
    fvmptf.3
    fveq2d
    @10
    fvmptf
    mpan2
    syl5eq
    cC
    cid
    fvprc
    sylan9eq
    expcom
    syl5
    cA
    cF
    ndmfv
    pm2.61d1
end
