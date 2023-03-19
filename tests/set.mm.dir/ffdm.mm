include "wf.mm"
include "cdm.mm"
include "wss.mm"
include "fdm.mm"
include "feq2d.mm"
include "ibir.mm"
include "wceq.mm"
include "eqimss.mm"
include "syl.mm"
include "jca.mm"

theorem ffdm
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A --> B -> ( F : dom F --> B /\ dom F C_ A ) )

  proof
    cA
    cB
    cF
    wf
    #
    cF
    cdm
    #
    cB
    cF
    wf
    #
    @1
    cA
    wss
    #
    @0
    @2
    @0
    @1
    cA
    cB
    cF
    cA
    cB
    cF
    fdm
    #
    feq2d
    ibir
    @0
    @1
    cA
    wceq
    @3
    @4
    @1
    cA
    eqimss
    syl
    jca
end
