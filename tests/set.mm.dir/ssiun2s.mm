include "ciun.mm"
include "wss.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfss.mm"
include "cv.mm"
include "wceq.mm"
include "sseq1d.mm"
include "ssiun2.mm"
include "vtoclgaf.mm"

theorem ssiun2s
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ssiun2s.1: |- ( x = C -> B = D )

  disjoint A x
  disjoint C x
  disjoint D x
  assert |- ( C e. A -> D C_ U_ x e. A B )

  proof
    cB
    vx
    cA
    cB
    ciun
    #
    wss
    cD
    @0
    wss
    vx
    cC
    cA
    vx
    cC
    nfcv
    vx
    cD
    @0
    vx
    cD
    nfcv
    vx
    cA
    cB
    nfiu1
    nfss
    vx
    cv
    cC
    wceq
    cB
    cD
    @0
    ssiun2s.1
    sseq1d
    vx
    cA
    cB
    ssiun2
    vtoclgaf
end
