include "nfcv.mm"
include "cvv.mm"
include "cmpt.mm"
include "crdg.mm"
include "wceq.mm"
include "cbvmptv.mm"
include "rdgeq1.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "rdgsucmptf.mm"

theorem rdgsucmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cV: class V
  assume rdgsucmpt2.1: |- F = rec ( ( x e. _V |-> C ) , A )
  assume rdgsucmpt2.2: |- ( y = x -> E = C )
  assume rdgsucmpt2.3: |- ( y = ( F ` B ) -> E = D )

  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  disjoint E x
  assert |- ( ( B e. On /\ D e. V ) -> ( F ` suc B ) = D )

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
    vy
    cvv
    cE
    cmpt
    #
    cA
    crdg
    #
    rdgsucmpt2.1
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
    rdgsucmpt2.2
    cbvmptv
    cA
    @2
    @0
    rdgeq1
    ax-mp
    eqtr4i
    rdgsucmpt2.3
    rdgsucmptf
end
