include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "cfv.mm"
include "cvv.mm"
include "cmpt.mm"
include "crdg.mm"
include "rdgsuc.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "wceq.mm"
include "fvex.mm"
include "nfmpt1.mm"
include "nfrdg.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "eqid.mm"
include "fvmptf.mm"
include "mpan.mm"
include "sylan9eq.mm"

theorem rdgsucmptf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  assume rdgsucmptf.1: |- F/_ x A
  assume rdgsucmptf.2: |- F/_ x B
  assume rdgsucmptf.3: |- F/_ x D
  assume rdgsucmptf.4: |- F = rec ( ( x e. _V |-> C ) , A )
  assume rdgsucmptf.5: |- ( x = ( F ` B ) -> C = D )


  assert |- ( ( B e. On /\ D e. V ) -> ( F ` suc B ) = D )

  proof
    cB
    con0
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
    cfv
    cB
    @7
    cfv
    #
    @5
    cfv
    @3
    @6
    cA
    cB
    @5
    rdgsuc
    @2
    cF
    @7
    rdgsucmptf.4
    fveq1i
    @4
    @8
    @5
    cB
    cF
    @7
    rdgsucmptf.4
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
    @7
    rdgsucmptf.4
    vx
    cA
    @5
    vx
    cvv
    cC
    nfmpt1
    rdgsucmptf.1
    nfrdg
    nfcxfr
    rdgsucmptf.2
    nffv
    rdgsucmptf.3
    rdgsucmptf.5
    @5
    eqid
    fvmptf
    mpan
    sylan9eq
end
