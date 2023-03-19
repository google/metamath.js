include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "cfv.mm"
include "cvv.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "frsuc.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "wceq.mm"
include "fvex.mm"
include "nfmpt1.mm"
include "nfrdg.mm"
include "nfcv.mm"
include "nfres.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "eqid.mm"
include "fvmptf.mm"
include "mpan.mm"
include "sylan9eq.mm"

theorem frsucmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  assume frsucmpt.1: |- F/_ x A
  assume frsucmpt.2: |- F/_ x B
  assume frsucmpt.3: |- F/_ x D
  assume frsucmpt.4: |- F = ( rec ( ( x e. _V |-> C ) , A ) |` _om )
  assume frsucmpt.5: |- ( x = ( F ` B ) -> C = D )


  assert |- ( ( B e. _om /\ D e. V ) -> ( F ` suc B ) = D )

  proof
    cB
    com
    wcel
    #
    cD
    cV
    wcel
    #
    cB
    csuc
    #
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    vx
    cvv
    cC
    cmpt
    #
    cfv
    #
    cD
    @0
    @2
    @5
    cA
    crdg
    #
    com
    cres
    #
    cfv
    cB
    @8
    cfv
    #
    @5
    cfv
    @3
    @6
    cA
    cB
    @5
    frsuc
    @2
    cF
    @8
    frsucmpt.4
    fveq1i
    @4
    @9
    @5
    cB
    cF
    @8
    frsucmpt.4
    fveq1i
    fveq2i
    3eqtr4g
    @4
    cvv
    wcel
    @1
    @6
    cD
    wceq
    cB
    cF
    fvex
    vx
    @4
    cC
    cD
    cvv
    @5
    cV
    vx
    cB
    cF
    vx
    cF
    @8
    frsucmpt.4
    vx
    @7
    com
    vx
    cA
    @5
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
    @5
    eqid
    fvmptf
    mpan
    sylan9eq
end
