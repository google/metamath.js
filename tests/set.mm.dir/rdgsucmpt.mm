include "nfcv.mm"
include "rdgsucmptf.mm"

theorem rdgsucmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cV: class V
  assume rdgsucmpt.1: |- F = rec ( ( x e. _V |-> C ) , A )
  assume rdgsucmpt.2: |- ( x = ( F ` B ) -> C = D )

  disjoint A x
  disjoint B x
  disjoint D x
  assert |- ( ( B e. On /\ D e. V ) -> ( F ` suc B ) = D )

  proof
    vx
    cA
    cB
    cC
    cD
    cF
    cV
    vx
    cA
    nfcv
    vx
    cB
    nfcv
    vx
    cD
    nfcv
    rdgsucmpt.1
    rdgsucmpt.2
    rdgsucmptf
end
