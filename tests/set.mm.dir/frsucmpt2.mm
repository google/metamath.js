include "nfcv.mm"
include "cvv.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "wceq.mm"
include "cbvmptv.mm"
include "rdgeq1.mm"
include "ax-mp.mm"
include "reseq1i.mm"
include "eqtr4i.mm"
include "frsucmpt.mm"

theorem frsucmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cV: class V
  assume frsucmpt2.1: |- F = ( rec ( ( x e. _V |-> C ) , A ) |` _om )
  assume frsucmpt2.2: |- ( y = x -> E = C )
  assume frsucmpt2.3: |- ( y = ( F ` B ) -> E = D )

  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  disjoint E x
  assert |- ( ( B e. _om /\ D e. V ) -> ( F ` suc B ) = D )

  proof
    vy
    cA
    cB
    cE
    cD
    cF
    cV
    vy
    cA
    nfcv
    vy
    cB
    nfcv
    vy
    cD
    nfcv
    cF
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
    vy
    cvv
    cE
    cmpt
    #
    cA
    crdg
    #
    com
    cres
    frsucmpt2.1
    @3
    @1
    com
    @2
    @0
    wceq
    @3
    @1
    wceq
    vy
    vx
    cvv
    cE
    cC
    frsucmpt2.2
    cbvmptv
    cA
    @2
    @0
    rdgeq1
    ax-mp
    reseq1i
    eqtr4i
    frsucmpt2.3
    frsucmpt
end
