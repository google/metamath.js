include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "csuc.mm"
include "cfv.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "c0.mm"
include "fveq1i.mm"
include "cdm.mm"
include "wceq.mm"
include "wfn.mm"
include "frfnom.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "peano2b.mm"
include "frsuc.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "nfmpt1.mm"
include "nfrdg.mm"
include "nfcv.mm"
include "nfres.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "eqid.mm"
include "fvmptnf.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "syl5bir.mm"
include "syl5bi.mm"
include "ndmfv.mm"
include "pm2.61d1.mm"
include "syl5eq.mm"

theorem frsucmptn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume frsucmpt.1: |- F/_ x A
  assume frsucmpt.2: |- F/_ x B
  assume frsucmpt.3: |- F/_ x D
  assume frsucmpt.4: |- F = ( rec ( ( x e. _V |-> C ) , A ) |` _om )
  assume frsucmpt.5: |- ( x = ( F ` B ) -> C = D )


  assert |- ( -. D e. _V -> ( F ` suc B ) = (/) )

  proof
    cD
    cvv
    wcel
    wn
    #
    cB
    csuc
    #
    cF
    cfv
    @1
    vx
    cvv
    cC
    cmpt
    #
    cA
    crdg
    #
    com
    cres
    #
    cfv
    #
    c0
    @1
    cF
    @4
    frsucmpt.4
    fveq1i
    @0
    @1
    @4
    cdm
    #
    wcel
    #
    @5
    c0
    wceq
    #
    @7
    @1
    com
    wcel
    #
    @0
    @8
    @6
    com
    @1
    @4
    com
    wfn
    @6
    com
    wceq
    cA
    @2
    frfnom
    com
    @4
    fndm
    ax-mp
    eleq2i
    @9
    cB
    com
    wcel
    #
    @0
    @8
    cB
    peano2b
    @0
    @10
    @8
    @10
    @0
    @5
    cB
    cF
    cfv
    #
    @2
    cfv
    #
    c0
    @10
    @5
    cB
    @4
    cfv
    #
    @2
    cfv
    @12
    cA
    cB
    @2
    frsuc
    @11
    @13
    @2
    cB
    cF
    @4
    frsucmpt.4
    fveq1i
    fveq2i
    syl6eqr
    vx
    @11
    cC
    cD
    cvv
    @2
    vx
    cB
    cF
    vx
    cF
    @4
    frsucmpt.4
    vx
    @3
    com
    vx
    cA
    @2
    vx
    cvv
    cC
    nfmpt1
    frsucmpt.1
    nfrdg
    vx
    com
    nfcv
    nfres
    nfcxfr
    frsucmpt.2
    nffv
    frsucmpt.3
    frsucmpt.5
    @2
    eqid
    fvmptnf
    sylan9eqr
    ex
    syl5bir
    syl5bi
    @1
    @4
    ndmfv
    pm2.61d1
    syl5eq
end
