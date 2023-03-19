include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "snidg.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "elsng.mm"
include "sylibd.mm"

theorem sneqrg
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( { A } = { B } -> A = B ) )

  proof
    cA
    cV
    wcel
    #
    cA
    csn
    #
    cB
    csn
    #
    wceq
    #
    cA
    @2
    wcel
    #
    cA
    cB
    wceq
    @0
    cA
    @1
    wcel
    @3
    @4
    cA
    cV
    snidg
    @1
    @2
    cA
    eleq2
    syl5ibcom
    cA
    cB
    cV
    elsng
    sylibd
end
